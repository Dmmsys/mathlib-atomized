/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.App
public meta import Lean.Elab.ConfigEval
public meta import Mathlib.Lean.Expr.Basic
public import Mathlib.Util.AddRelatedDecl
public import Mathlib.Tactic.Simps.NotationClass
public import Mathlib.Tactic.Translate.Attributes

/-!
# Simps attribute

This file defines the `@[simps]` attribute, to automatically generate `simp` lemmas
reducing a definition when projections are applied to it.

## Implementation Notes

There are three attributes being defined here
* `@[simps]` is the attribute for objects of a structure or instances of a class. It will
  automatically generate simplification lemmas for each projection of the object/instance that
  contains data. See the doc strings for `Lean.Parser.Attr.simps` and `Simps.Config`
  for more details and configuration options.
* `structureExt` (just an environment extension, not actually an attribute)
  is automatically added to structures that have been used in `@[simps]`
  at least once. This attribute contains the data of the projections used for this structure
  by all following invocations of `@[simps]`.
* `@[notation_class]` should be added to all classes that define notation, like `Mul` and
  `Zero`. This specifies that the projections that `@[simps]` used are the projections from
  these notation classes instead of the projections of the superclasses.
  Example: if `Mul` is tagged with `@[notation_class]` then the projection used for `Semigroup`
  will be `fun α hα ↦ @Mul.mul α (@Semigroup.toMul α hα)` instead of `@Semigroup.mul`.
  [this is not correctly implemented in Lean 4 yet]

### Possible Future Improvements
* If multiple declarations are generated from a `simps` without explicit projection names, then
  only the first one is shown when mousing over `simps`.

## Changes w.r.t. Lean 3

There are some small changes in the attribute. None of them should have great effects
* The attribute will now raise an error if it tries to generate a lemma when there already exists
  a lemma with that name (in Lean 3 it would generate a different unique name)
* `transparency.none` has been replaced by `TransparencyMode.reducible`
* The `attr` configuration option has been split into `isSimp` and `attrs` (for extra attributes)
* Because Lean 4 uses bundled structures, this means that `simps` applied to anything that
  implements a notation class will almost certainly require a user-provided custom simps projection.

## Tags

structures, projections, simp, simplifier, generates declarations
-/

public meta section
open Lean Elab Parser Command
open Meta hiding Config
open Elab.Term hiding mkConst

/--
Definition of `NameStruct` / `NameStruct` 的定义

English:
structure NameStruct
  parameters: where
  axioms and operations (2):
    - parent : Name
    - components : List String

中文:
结构 NameStruct
  参数: where
  公理与运算 (2 个):
    - parent : Name
    - components : 列表 String
-/
private structure NameStruct where
  /-- The namespace that the final name will reside in. -/
  parent : Name
  /-- A list of pieces to be joined by `toName`. -/
  components : List String

/--
Definition of `NameStruct.toName` / `NameStruct.toName` 的定义

English:
definition NameStruct.toName
  signature: (n : NameStruct)
  body: Name.mkStr n.parent
    match n.components with
    | [] => ""
    | [x] => s!"{x}_def"
    | e => "_".intercalate e

中文:
定义 NameStruct.toName
  签名: (n : NameStruct)
  定义体: Name.mkStr n.parent
    match n.components with
    | [] => ""
    | [x] => s!"{x}_def"
    | e => "_".intercalate e
-/
private def NameStruct.toName (n : NameStruct) : Name :=
Name.mkStr n.parent
    match n.components with
    | [] => ""
    | [x] => s!"{x}_def"
    | e => "_".intercalate e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe NameStruct Name
  body: NameStruct.toName

中文:
实例 :
  签名: Coe NameStruct Name
  定义体: NameStruct.toName
-/
private instance : Coe NameStruct Name where coe := NameStruct.toName

/--
Definition of `NameStruct.update` / `NameStruct.update` 的定义

English:
definition NameStruct.update
  signature: (nm : NameStruct) (s : String) (isPrefix : Bool := false)
  body: { nm with components := if isPrefix then s :: nm.components else nm.components ++ [s] }

中文:
定义 NameStruct.update
  签名: (nm : NameStruct) (s : String) (isPrefix : 布尔值 := false)
  定义体: { nm with components := if isPrefix then s :: nm.components else nm.components ++ [s] }
-/
private def NameStruct.update (nm : NameStruct) (s : String) (isPrefix : Bool := false) :
    NameStruct :=
  { nm with components := if isPrefix then s :: nm.components else nm.components ++ [s] }

-- move
namespace Lean.Meta
open Tactic Simp
/--
Definition of `mkSimpContextResult` / `mkSimpContextResult` 的定义

English:
definition mkSimpContextResult
  signature: (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
  body: do
  match dischargeWrapper with
  | .default => pure ()
  | _ =>
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    getSimpTheorems
  let simprocs := #[← if simpOnly then pure {} else Simp.getSimprocs]
  let congrTheorems ← getSimpCongrTheorems
  let ctx : Simp.Context ← Simp.mkContext cfg
    (simpTheorems := #[simpTheorems])
    (congrTheorems := congrTheorems)
  if !hasStar then
    return { ctx, simprocs, dischargeWrapper }
  else
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := ctx.setSimpTheorems simpTheorems
    return { ctx, simprocs, dischargeWrapper }

中文:
定义 mkSimpContextResult
  签名: (cfg : Meta.Simp.余nfig := {}) (simpOnly := false) (kind := SimpKind.simp)
  定义体: do
  match dischargeWrapper with
  | .default => pure ()
  | _ =>
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    getSimpTheorems
  let simprocs := #[← if simpOnly then pure {} else Simp.getSimprocs]
  let congrTheorems ← getSimpCongrTheorems
  let ctx : Simp.Context ← Simp.mkContext cfg
    (simpTheorems := #[simpTheorems])
    (congrTheorems := congrTheorems)
  if !hasStar then
    return { ctx, simprocs, dischargeWrapper }
  else
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := ctx.setSimpTheorems simpTheorems
    return { ctx, simprocs, dischargeWrapper }

Depends on / 依赖: SimpKind, SimpKind.simp, simpOnly
-/
def mkSimpContextResult (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
    (dischargeWrapper := DischargeWrapper.default) (hasStar := false) :
    MetaM MkSimpContextResult := do
  match dischargeWrapper with
  | .default => pure ()
  | _ =>
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    getSimpTheorems
  let simprocs := #[← if simpOnly then pure {} else Simp.getSimprocs]
  let congrTheorems ← getSimpCongrTheorems
  let ctx : Simp.Context ← Simp.mkContext cfg
    (simpTheorems := #[simpTheorems])
    (congrTheorems := congrTheorems)
  if !hasStar then
    return { ctx, simprocs, dischargeWrapper }
  else
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := ctx.setSimpTheorems simpTheorems
    return { ctx, simprocs, dischargeWrapper }

/--
Definition of `mkSimpContext` / `mkSimpContext` 的定义

English:
definition mkSimpContext
  signature: (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
  body: do
  let data ← mkSimpContextResult cfg simpOnly kind dischargeWrapper hasStar
  return data.ctx

中文:
定义 mkSimpContext
  签名: (cfg : Meta.Simp.余nfig := {}) (simpOnly := false) (kind := SimpKind.simp)
  定义体: do
  let data ← mkSimpContextResult cfg simpOnly kind dischargeWrapper hasStar
  return data.ctx

Depends on / 依赖: SimpKind, SimpKind.simp, simpOnly
-/
def mkSimpContext (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
    (dischargeWrapper := DischargeWrapper.default) (hasStar := false) :
    MetaM Simp.Context := do
  let data ← mkSimpContextResult cfg simpOnly kind dischargeWrapper hasStar
  return data.ctx

end Lean.Meta

namespace Lean.Parser
namespace Attr


/-! Declare notation classes. -/
attribute [notation_class add] HAdd
attribute [notation_class mul] HMul
attribute [notation_class sub] HSub
attribute [notation_class div] HDiv
attribute [notation_class mod] HMod
attribute [notation_class append] HAppend
attribute [notation_class pow Simps.copyFirst] HPow
attribute [notation_class andThen] HAndThen
attribute [notation_class] Neg Inv Dvd LE LT HasEquiv HasSubset HasSSubset Union Inter SDiff Insert
  Singleton Sep Membership
attribute [notation_class one Simps.findOneArgs] OfNat
attribute [notation_class zero Simps.findZeroArgs] OfNat

/-- `@[simps (attr := attr1, attr2, ...)]` adds additional attributes to all lemmas
generated by `simps`. -/
syntax simpsConfigAttrItem := atomic(" (" &"attr" " := ") Parser.Term.attrInstance,* ")"
/-- Configuration items for `@[simps]` attribute. -/
syntax simpsConfigItem := simpsConfigAttrItem > Term.configItem
/-- Configuration for `@[simps]` attribute. -/
syntax simpsConfig := many(simpsConfigItem)
/-- Arguments to `@[simps]` attribute. -/
syntax simpsArgsRest := simpsConfig (ppSpace ident)*

/-- The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example:
```lean
@[simps] def foo : ℕ × ℤ := (1, 2)
```
derives two `simp` lemmas:
```lean
@[simp] lemma foo_fst : foo.fst = 1
@[simp] lemma foo_snd : foo.snd = 2
```

* It does not derive `simp` lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If the structure has a coercion to either sorts or functions, and this is defined to be one
  of the projections, then this coercion will be used instead of the projection.
* If the structure is a class that has an instance to a notation class, like `Neg` or `Mul`,
  then this notation is used instead of the corresponding projection.
* You can specify custom projections, by giving a declaration with name
  `{StructureName}.Simps.{projectionName}`. See Note [custom simps projection].

  Example:
  ```lean
  def Equiv.Simps.invFun (e : α ≃ β) : β → α := e.symm
  @[simps] def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma Equiv.trans_toFun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma Equiv.trans_invFun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* You can specify custom projection names, by specifying the new projection names using
  `initialize_simps_projections`.
  Example: `initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)`.
  See `initialize_simps_projections` for more information.

* If one of the fields itself is a structure, this command will recursively create
  `simp` lemmas for all fields in that structure.
  * Exception: by default it will not recursively create `simp` lemmas for fields in the structures
    `Prod`, `PProd`, and `Opposite`. You can give explicit projection names or change the value of
    `Simps.Config.notRecursive` to override this behavior.

  Example:
  ```lean
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : Prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_snd_fst : foo.snd.fst = 3
  @[simp] lemma foo_snd_snd : foo.snd.snd = 4
  ```

* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections.
* Recursive projection names can be specified using `proj1_proj2_proj3`.
  This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.

  Example:
  ```lean
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : Prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure EquivPlusData (α β) extends α ≃ β where
    data : Bool
  @[simps] def EquivPlusData.rfl {α} : EquivPlusData α α := { Equiv.refl α with data := true }
  ```
  generates the following:
  ```lean
  @[simp] lemma bar_toEquiv : ∀ {α : Sort*}, bar.toEquiv = Equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort*}, bar.data = true
  ```
  This is true, even though Lean inserts an eta-expanded version of `Equiv.refl α` in the
  definition of `bar`.
* You can add additional attributes to all lemmas generated by `simps` using e.g.
  `@[simps (attr := grind =)]`.
* For configuration options, see the doc string of `Simps.Config`.
* The precise syntax is `simps config ident*`, where `config` declares configuration options,
  and `ident*` is a list of desired projection names.
  The `config` can contain `(attr := a)` entries, where `a` is a list of attributes.
* Configuration options can be given using `(config := e)` where `e : Simps.Config`,
  or by specifying options directly, like `-fullyApplied` or `(notRecursive := [])`.
* `@[simps]` reduces let-expressions where necessary.
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates. The same can be achieved by using `@[simps?]`.
* Use `@[to_additive (attr := simps)]` to apply both `to_additive` and `simps` to a definition
  This will also generate the additive versions of all `simp` lemmas.
-/
/- If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens, so is not included in the official doc). -/
syntax (name := simps) "simps" "!"? "?"? simpsArgsRest : attr

@[inherit_doc simps] macro "simps?" rest:simpsArgsRest : attr => `(attr| simps ? $rest)
@[inherit_doc simps] macro "simps!" rest:simpsArgsRest : attr => `(attr| simps ! $rest)
@[inherit_doc simps] macro "simps!?" rest:simpsArgsRest : attr => `(attr| simps ! ? $rest)
@[inherit_doc simps] macro "simps?!" rest:simpsArgsRest : attr => `(attr| simps ! ? $rest)

end Attr

/-- Linter to check that `simps!` is used when needed -/
register_option linter.simpsNoConstructor : Bool := {
  defValue := true
  descr := "Linter to check that `simps!` is used" }

/-- Linter to check that no unused custom declarations are declared for simps. -/
register_option linter.simpsUnusedCustomDeclarations : Bool := {
  defValue := true
  descr := "Linter to check that no unused custom declarations are declared for simps" }

namespace Command

/-- Syntax for renaming a projection in `initialize_simps_projections`. -/
syntax simpsRule.rename := ident " -> " ident
/-- Syntax for making a projection non-default in `initialize_simps_projections`. -/
syntax simpsRule.erase := "-" ident
/-- Syntax for making a projection default in `initialize_simps_projections`. -/
syntax simpsRule.add := "+" ident
/-- Syntax for making a projection prefix. -/
syntax simpsRule.prefix := &"as_prefix " ident
/-- Syntax for a single rule in `initialize_simps_projections`. -/
syntax simpsRule := simpsRule.prefix > simpsRule.rename > simpsRule.erase > simpsRule.add
/-- Syntax for `initialize_simps_projections`. -/
syntax simpsProj := ppSpace ident (" (" simpsRule,+ ")")?

/--
This command allows customisation of the lemmas generated by `simps`.

By default, tagging a definition of an element `myObj` of a structure `MyStruct` with `@[simps]`
generates one `@[simp]` lemma `myObj_myProj` for each projection `myProj` of `MyStruct`. There are a
few exceptions to this general rule:
* For algebraic structures, we will automatically use the notation (like `Mul`)
  for the projections if such an instance is available.
* By default, the projections to parent structures are not default projections,
  but all the data-carrying fields are (including those in parent structures).

This default behavior is customisable as such:
* You can disable a projection by default by running
  `initialize_simps_projections MulEquiv (-invFun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user (as in
  `@[simps invFun] def myEquiv : MulEquiv _ _ := _`).
* Conversely, you can enable a projection by default by running
  `initialize_simps_projections MulEquiv (+toEquiv)`.
* You can specify custom names by writing e.g.
  `initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)`.
* If you want the projection name added as a prefix in the generated lemma name, you can use
  `as_prefix fieldName`:
  `initialize_simps_projections MulEquiv (toFun → coe, as_prefix coe)`
  Note that this does not influence the parsing of projection names: if you have a declaration
  `foo` and you want to apply the projections `snd`, `coe` (which is a prefix) and `fst`, in that
  order you can run `@[simps snd_coe_fst] def foo ...` and this will generate a lemma with the
  name `coe_foo_snd_fst`.

Here are a few extra pieces of information:
* Run `initialize_simps_projections?` (or `set_option trace.simps.verbose true`)
  to see the generated projections.
* Running `initialize_simps_projections MyStruct` without arguments is not necessary, it has the
  same effect if you just add `@[simps]` to a declaration.
* It is recommended to call `@[simps]` or `initialize_simps_projections` in the same file as the
  structure declaration. Otherwise, the projections could be generated multiple times in different
  files.

Some common uses:
* If you define a new homomorphism-like structure (like `MulHom`) you can just run
  `initialize_simps_projections` after defining the `DFunLike` instance (or instance that implies
  a `DFunLike` instance).
  ```
    instance {mM : Mul M} {mN : Mul N} : FunLike (MulHom M N) M N := ...
    initialize_simps_projections MulHom (toFun → apply)
  ```
  This will generate `foo_apply` lemmas for each declaration `foo`.
* If you prefer `coe_foo` lemmas that state equalities between functions, use
  `initialize_simps_projections MulHom (toFun → coe, as_prefix coe)`
  In this case you have to use `@[simps -fullyApplied]` whenever you call `@[simps]`.
* You can also initialize to use both, in which case you have to choose which one to use by default,
  by using either of the following
  ```
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -coe)
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps -fullyApplied coe]` and in
  the second case you can get both lemmas using `@[simps -fullyApplied, simps apply]`.
* If you declare a new homomorphism-like structure (like `RelEmbedding`),
  then `initialize_simps_projections` will automatically find any `DFunLike` coercions
  that will be used as the default projection for the `toFun` field.
  ```
    initialize_simps_projections relEmbedding (toFun → apply)
  ```
* If you have an isomorphism-like structure (like `Equiv`) you often want to define a custom
  projection for the inverse:
  ```
    def Equiv.Simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)
  ```
-/
syntax (name := initialize_simps_projections)
  "initialize_simps_projections" "?"? simpsProj : command

@[inherit_doc «initialize_simps_projections»]
macro "initialize_simps_projections?" rest:simpsProj : command =>
  `(initialize_simps_projections ? $rest)

end Command
end Lean.Parser

initialize registerTraceClass `simps.verbose
initialize registerTraceClass `simps.debug

namespace Simps

/--
Definition of `ProjectionData` / `ProjectionData` 的定义

English:
structure ProjectionData
  parameters: where
  axioms and operations (5):
    - name : Name
    - expr : Expr
    - projNrs : List Nat
    - isDefault : Bool
    - isPrefix : Bool

中文:
结构 ProjectionData
  参数: where
  公理与运算 (5 个):
    - name : Name
    - expr : Expr
    - projNrs : 列表 自然数
    - isDefault : 布尔值
    - isPrefix : 布尔值
-/
structure ProjectionData where
  /-- The name used in the generated `simp` lemmas -/
  name : Name
  /-- An Expression used by simps for the projection. It must be definitionally equal to an original
  projection (or a composition of multiple projections).
  These Expressions can contain the universe parameters specified in the first argument of
  `structureExt`. -/
  expr : Expr
  /-- A list of natural numbers, which is the projection number(s) that have to be applied to the
  Expression. For example the list `[0, 1]` corresponds to applying the first projection of the
  structure, and then the second projection of the resulting structure (this assumes that the
  target of the first projection is a structure with at least two projections).
  The composition of these projections is required to be definitionally equal to the provided
  Expression. -/
  projNrs : List Nat
  /-- A Boolean specifying whether `simp` lemmas are generated for this projection by default. -/
  isDefault : Bool
  /-- A Boolean specifying whether this projection is written as prefix. -/
  isPrefix : Bool
  deriving Inhabited

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToMessageData ProjectionData

中文:
实例 :
  签名: ToMessageData ProjectionData
-/
instance : ToMessageData ProjectionData where toMessageData
| ⟨a, b, c, d, e⟩ => .group .nest 1
    "⟨" ++ .joinSep [toMessageData a, toMessageData b, toMessageData c, toMessageData d,
      toMessageData e] ("," ++ Format.line) ++ "⟩"

/--
The `Simps.structureExt` environment extension specifies the preferred projections of the given
structure, used by the `@[simps]` attribute.
- You can generate this with the command `initialize_simps_projections`.
- If not generated, the `@[simps]` attribute will generate this automatically.
- To change the default value, see Note [custom simps projection].
- The first argument is the list of names of the universe variables used in the structure
- The second argument is an array that consists of the projection data for each projection.
-/
initialize structureExt : NameMapExtension (List Name × Array ProjectionData) ←
  registerNameMapExtension (List Name × Array ProjectionData)

/--
Definition of `ParsedProjectionData` / `ParsedProjectionData` 的定义

English:
structure ParsedProjectionData
  parameters: where
  axioms and operations (9):
    - strName : Name
    - strStx : Syntax  [default: .missing]
    - newName : Name
    - newStx : Syntax  [default: .missing]
    - isDefault : Bool  [default: true]
    - isPrefix : Bool  [default: false]
    - expr? : Option Expr  [default: none]
    - projNrs : Array Nat  [default: #[]]
    - isCustom : Bool  [default: false]

中文:
结构 ParsedProjectionData
  参数: where
  公理与运算 (9 个):
    - strName : Name
    - strStx : Syntax  [默认: .missing]
    - newName : Name
    - newStx : Syntax  [默认: .missing]
    - isDefault : 布尔值  [默认: true]
    - isPrefix : 布尔值  [默认: false]
    - expr? : 选项类型 Expr  [默认: none]
    - projNrs : 数组 自然数  [默认: #[]]
    - isCustom : 布尔值  [默认: false]

Depends on / 依赖: missing
-/
structure ParsedProjectionData where
  /-- name for this projection used in the structure definition -/
  strName : Name
  /-- syntax that might have provided `strName` -/
  strStx : Syntax := .missing
  /-- name for this projection used in the generated `simp` lemmas -/
  newName : Name
  /-- syntax that provided `newName` -/
  newStx : Syntax := .missing
  /-- will simp lemmas be generated for with (without specifically naming this?) -/
  isDefault : Bool := true
  /-- is the projection name a prefix? -/
  isPrefix : Bool := false
  /-- projection expression -/
  expr? : Option Expr := none
  /-- the list of projection numbers this expression corresponds to -/
  projNrs : Array Nat := #[]
  /-- is this a projection that is changed by the user? -/
  isCustom : Bool := false

/--
Definition of `ParsedProjectionData.toProjectionData` / `ParsedProjectionData.toProjectionData` 的定义

English:
definition ParsedProjectionData.toProjectionData
  signature: (p : ParsedProjectionData)
  body: { p with name := p.newName, expr := p.expr?.getD default, projNrs := p.projNrs.toList }

中文:
定义 ParsedProjectionData.toProjectionData
  签名: (p : ParsedProjectionData)
  定义体: { p with name := p.newName, expr := p.expr?.getD default, projNrs := p.projNrs.toList }

Depends on / 依赖: newName, p.expr, p.newName, p.projNrs.toList, projNrs, toList
-/
def ParsedProjectionData.toProjectionData (p : ParsedProjectionData) : ProjectionData :=
  { p with name := p.newName, expr := p.expr?.getD default, projNrs := p.projNrs.toList }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToMessageData ParsedProjectionData

中文:
实例 :
  签名: ToMessageData ParsedProjectionData
-/
instance : ToMessageData ParsedProjectionData where toMessageData
| ⟨x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉⟩ => .group .nest 1
    "⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂, toMessageData x₃, toMessageData x₄,
      toMessageData x₅, toMessageData x₆, toMessageData x₇, toMessageData x₈, toMessageData x₉]
    ("," ++ Format.line) ++ "⟩"

/--
Inductive type `ProjectionRule` / 归纳类型 `ProjectionRule`

English:
inductive ProjectionRule
  parameters: where
  constructors (4):
    - rename: (oldName : Name) (oldStx : Syntax) (newName : Name) (newStx : Syntax) : ProjectionRule
    - add: Name -> Syntax -> ProjectionRule
    - erase: Name -> Syntax -> ProjectionRule
    - prefix: Name -> Syntax -> ProjectionRule

中文:
归纳类型 ProjectionRule
  参数: where
  构造子 (4 个):
    - rename: (oldName : Name) (oldStx : Syntax) (newName : Name) (newStx : Syntax) : ProjectionRule
    - add: Name -> Syntax -> ProjectionRule
    - erase: Name -> Syntax -> ProjectionRule
    - prefix: Name -> Syntax -> ProjectionRule
-/
inductive ProjectionRule where
  /-- A renaming rule `before→after` or
    Each name comes with the syntax used to write the rule,
    which is used to declare hover information. -/
  | rename (oldName : Name) (oldStx : Syntax) (newName : Name) (newStx : Syntax) :
      ProjectionRule
  /-- An adding rule `+fieldName` -/
  | add : Name -> Syntax -> ProjectionRule
  /-- A hiding rule `-fieldName` -/
  | erase : Name -> Syntax -> ProjectionRule
  /-- A prefix rule `prefix fieldName` -/
  | prefix : Name -> Syntax -> ProjectionRule

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToMessageData ProjectionRule

中文:
实例 :
  签名: ToMessageData ProjectionRule
-/
instance : ToMessageData ProjectionRule where toMessageData
| .rename x₁ x₂ x₃ x₄ => .group .nest 1
    "rename ⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂, toMessageData x₃, toMessageData x₄]
      ("," ++ Format.line) ++ "⟩"
| .add x₁ x₂ => .group .nest 1
    "+⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"
| .erase x₁ x₂ => .group .nest 1
    "-⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"
| .prefix x₁ x₂ => .group .nest 1
    "prefix ⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"

/--
Definition of `projectionsInfo` / `projectionsInfo` 的定义

English:
definition projectionsInfo
  signature: (l : List ProjectionData) (pref : String) (str : Name)
  body: let ⟨defaults, nondefaults⟩ := l.partition (·.isDefault)
  let toPrint : List MessageData :=
    defaults.map fun s =>
      let prefixStr := if s.isPrefix then "(prefix) " else ""
      m!"Projection {prefixStr}{s.name}: {s.expr}"
  let print2 : MessageData :=
String.join (nondefaults.map fun nm : ProjectionData => toString nm.1).intersperse ", "
  let toPrint :=
    toPrint ++
      if nondefaults.isEmpty then [] else
      [("No lemmas are generated for the projections: " : MessageData) ++ print2 ++ "."]
  let toPrint := MessageData.joinSep toPrint ("\n" : MessageData)
  m!"{pref} {str}:\n{toPrint}"

中文:
定义 projectionsInfo
  签名: (l : 列表 ProjectionData) (pref : String) (str : Name)
  定义体: let ⟨defaults, nondefaults⟩ := l.partition (·.isDefault)
  let toPrint : List MessageData :=
    defaults.map fun s =>
      let prefixStr := if s.isPrefix then "(prefix) " else ""
      m!"Projection {prefixStr}{s.name}: {s.expr}"
  let print2 : MessageData :=
String.join (nondefaults.map fun nm : ProjectionData => toString nm.1).intersperse ", "
  let toPrint :=
    toPrint ++
      if nondefaults.isEmpty then [] else
      [("No lemmas are generated for the projections: " : MessageData) ++ print2 ++ "."]
  let toPrint := MessageData.joinSep toPrint ("\n" : MessageData)
  m!"{pref} {str}:\n{toPrint}"

Depends on / 依赖: MessageDat, MessageData, Projection, ProjectionData, String.join, defaults, defaults.map, generated, intersperse, isDefault, isEmpty, isPrefix, l.partition, lemmas, nondefaults, nondefaults.isEmpty, nondefaults.map, partition, prefix, prefixStr
-/
def projectionsInfo (l : List ProjectionData) (pref : String) (str : Name) : MessageData :=
  let ⟨defaults, nondefaults⟩ := l.partition (·.isDefault)
  let toPrint : List MessageData :=
    defaults.map fun s =>
      let prefixStr := if s.isPrefix then "(prefix) " else ""
      m!"Projection {prefixStr}{s.name}: {s.expr}"
  let print2 : MessageData :=
String.join (nondefaults.map fun nm : ProjectionData => toString nm.1).intersperse ", "
  let toPrint :=
    toPrint ++
      if nondefaults.isEmpty then [] else
      [("No lemmas are generated for the projections: " : MessageData) ++ print2 ++ "."]
  let toPrint := MessageData.joinSep toPrint ("\n" : MessageData)
  m!"{pref} {str}:\n{toPrint}"

/--
Definition of `findProjectionIndices` / `findProjectionIndices` 的定义

English:
definition findProjectionIndices
  signature: (strName projName : Name)
  body: do
  let env ← getEnv
  let some baseStr := findField? env strName projName |
    throwError "{strName} has no field {projName} in parent structure"
  let some fullProjName := getProjFnForField? env baseStr projName |
    throwError "no such field {projName}"
  let some pathToField := getPathToBaseStructure? env baseStr strName |
    throwError "no such field {projName}"
  let allProjs := pathToField ++ [fullProjName]
  return allProjs.map (env.getProjectionFnInfo? · |>.get!.i)

中文:
定义 findProjectionIndices
  签名: (strName projName : Name)
  定义体: do
  let env ← getEnv
  let some baseStr := findField? env strName projName |
    throwError "{strName} has no field {projName} in parent structure"
  let some fullProjName := getProjFnForField? env baseStr projName |
    throwError "no such field {projName}"
  let some pathToField := getPathToBaseStructure? env baseStr strName |
    throwError "no such field {projName}"
  let allProjs := pathToField ++ [fullProjName]
  return allProjs.map (env.getProjectionFnInfo? · |>.get!.i)
-/
def findProjectionIndices (strName projName : Name) : MetaM (List Nat) := do
  let env ← getEnv
  let some baseStr := findField? env strName projName |
    throwError "{strName} has no field {projName} in parent structure"
  let some fullProjName := getProjFnForField? env baseStr projName |
    throwError "no such field {projName}"
  let some pathToField := getPathToBaseStructure? env baseStr strName |
    throwError "no such field {projName}"
  let allProjs := pathToField ++ [fullProjName]
  return allProjs.map (env.getProjectionFnInfo? · |>.get!.i)

/--
Definition of `dropPrefixIfNotNumber?` / `dropPrefixIfNotNumber?` 的定义

English:
definition dropPrefixIfNotNumber?
  signature: (s : String) (pre : String)
  body: do
  let ret ← s.dropPrefix? pre
  -- flag is true when the remaining part is nonempty and starts with a digit.
  let flag := ret.toString.toList.head?.elim false Char.isDigit
  if flag then none else some ret

中文:
定义 dropPrefixIfNotNumber?
  签名: (s : String) (pre : String)
  定义体: do
  let ret ← s.dropPrefix? pre
  -- flag is true when the remaining part is nonempty and starts with a digit.
  let flag := ret.toString.toList.head?.elim false Char.isDigit
  if flag then none else some ret
-/
private def dropPrefixIfNotNumber? (s : String) (pre : String) : Option String.Slice := do
  let ret ← s.dropPrefix? pre
  -- flag is true when the remaining part is nonempty and starts with a digit.
  let flag := ret.toString.toList.head?.elim false Char.isDigit
  if flag then none else some ret

/--
Definition of `isPrefixOfAndNotNumber` / `isPrefixOfAndNotNumber` 的定义

English:
definition isPrefixOfAndNotNumber
  signature: (s p : String)
  body: (dropPrefixIfNotNumber? p s).isSome

中文:
定义 isPrefixOfAndNotNumber
  签名: (s p : String)
  定义体: (dropPrefixIfNotNumber? p s).isSome
-/
private def isPrefixOfAndNotNumber (s p : String) : Bool := (dropPrefixIfNotNumber? p s).isSome

/--
Definition of `splitOnNotNumber` / `splitOnNotNumber` 的定义

English:
definition splitOnNotNumber
  signature: (s delim : String)
  body: (process (s.splitOn delim).reverse "").reverse where
    process (arr : List String) (tail : String) := match arr with
      | [] => []
      | (x :: xs) =>
        -- flag is true when this segment is nonempty and starts with a digit.
        let flag := x.toList.head?.elim false Char.isDigit
        if flag then
          process xs (tail ++ delim ++ x)
        else
          List.cons (x ++ tail) (process xs "")

中文:
定义 splitOnNotNumber
  签名: (s delim : String)
  定义体: (process (s.splitOn delim).reverse "").reverse where
    process (arr : List String) (tail : String) := match arr with
      | [] => []
      | (x :: xs) =>
        -- flag is true when this segment is nonempty and starts with a digit.
        let flag := x.toList.head?.elim false Char.isDigit
        if flag then
          process xs (tail ++ delim ++ x)
        else
          List.cons (x ++ tail) (process xs "")
-/
private def splitOnNotNumber (s delim : String) : List String :=
  (process (s.splitOn delim).reverse "").reverse where
    process (arr : List String) (tail : String) := match arr with
      | [] => []
      | (x :: xs) =>
        -- flag is true when this segment is nonempty and starts with a digit.
        let flag := x.toList.head?.elim false Char.isDigit
        if flag then
          process xs (tail ++ delim ++ x)
        else
          List.cons (x ++ tail) (process xs "")

/--
Definition of `getCompositeOfProjectionsAux` / `getCompositeOfProjectionsAux` 的定义

English:
definition getCompositeOfProjectionsAux
  signature: (proj : String) (e : Expr) (pos : Array Nat)
  body: do
  let env ← getEnv
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let projs := getStructureFieldsFlattened env structName
  let projInfo := projs.toList.map fun p => do
    ((← dropPrefixIfNotNumber? proj (p.lastComponentAsString ++ "_")).toString, p)
  let some (projRest, projName) := projInfo.reduceOption.getLast? |
    throwError "Failed to find constructor {proj.dropEnd 1} in structure {structName}."
  let newE ← mkProjection e projName
  let newPos := pos ++ (← findProjectionIndices structName projName)
  -- we do this here instead of in a recursive call in order to not get an unnecessary eta-redex
  if projRest.isEmpty then
    let newE ← mkLambdaFVars args newE
    return (newE, newPos)
  let type ← inferType newE
  forallTelescopeReducing type fun typeArgs _tgt => do
    getCompositeOfProjectionsAux projRest (mkAppN newE typeArgs) newPos (args ++ typeArgs)

中文:
定义 getCompositeOfProjectionsAux
  签名: (proj : String) (e : Expr) (pos : 数组 自然数)
  定义体: do
  let env ← getEnv
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let projs := getStructureFieldsFlattened env structName
  let projInfo := projs.toList.map fun p => do
    ((← dropPrefixIfNotNumber? proj (p.lastComponentAsString ++ "_")).toString, p)
  let some (projRest, projName) := projInfo.reduceOption.getLast? |
    throwError "Failed to find constructor {proj.dropEnd 1} in structure {structName}."
  let newE ← mkProjection e projName
  let newPos := pos ++ (← findProjectionIndices structName projName)
  -- we do this here instead of in a recursive call in order to not get an unnecessary eta-redex
  if projRest.isEmpty then
    let newE ← mkLambdaFVars args newE
    return (newE, newPos)
  let type ← inferType newE
  forallTelescopeReducing type fun typeArgs _tgt => do
    getCompositeOfProjectionsAux projRest (mkAppN newE typeArgs) newPos (args ++ typeArgs)
-/
partial def getCompositeOfProjectionsAux (proj : String) (e : Expr) (pos : Array Nat)
    (args : Array Expr) : MetaM (Expr × Array Nat) := do
  let env ← getEnv
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let projs := getStructureFieldsFlattened env structName
  let projInfo := projs.toList.map fun p => do
    ((← dropPrefixIfNotNumber? proj (p.lastComponentAsString ++ "_")).toString, p)
  let some (projRest, projName) := projInfo.reduceOption.getLast? |
    throwError "Failed to find constructor {proj.dropEnd 1} in structure {structName}."
  let newE ← mkProjection e projName
  let newPos := pos ++ (← findProjectionIndices structName projName)
  -- we do this here instead of in a recursive call in order to not get an unnecessary eta-redex
  if projRest.isEmpty then
    let newE ← mkLambdaFVars args newE
    return (newE, newPos)
  let type ← inferType newE
  forallTelescopeReducing type fun typeArgs _tgt => do
    getCompositeOfProjectionsAux projRest (mkAppN newE typeArgs) newPos (args ++ typeArgs)

/--
Definition of `getCompositeOfProjections` / `getCompositeOfProjections` 的定义

English:
definition getCompositeOfProjections
  signature: (structName : Name) (proj : String)
  body: do
  let strExpr ← mkConstWithLevelParams structName
  let type ← inferType strExpr
  forallTelescopeReducing type fun typeArgs _ =>
  withLocalDeclD `x (mkAppN strExpr typeArgs) fun e =>
getCompositeOfProjectionsAux (proj ++ "_") e #[] typeArgs.push e

中文:
定义 getCompositeOfProjections
  签名: (structName : Name) (proj : String)
  定义体: do
  let strExpr ← mkConstWithLevelParams structName
  let type ← inferType strExpr
  forallTelescopeReducing type fun typeArgs _ =>
  withLocalDeclD `x (mkAppN strExpr typeArgs) fun e =>
getCompositeOfProjectionsAux (proj ++ "_") e #[] typeArgs.push e
-/
def getCompositeOfProjections (structName : Name) (proj : String) : MetaM (Expr × Array Nat) := do
  let strExpr ← mkConstWithLevelParams structName
  let type ← inferType strExpr
  forallTelescopeReducing type fun typeArgs _ =>
  withLocalDeclD `x (mkAppN strExpr typeArgs) fun e =>
getCompositeOfProjectionsAux (proj ++ "_") e #[] typeArgs.push e

/--
Definition of `mkParsedProjectionData` / `mkParsedProjectionData` 的定义

English:
definition mkParsedProjectionData
  signature: (structName : Name)
  body: do
  let env ← getEnv
  let projs := getStructureFields env structName
  if projs.size == 0 then
    throwError "Declaration {structName} is not a structure."
  let projData := projs.map fun fieldName => {
    strName := fieldName, newName := fieldName,
.isNone } isDefault := isSubobjectField? env structName fieldName
  let parentProjs := getStructureFieldsFlattened env structName false
  let parentProjs := parentProjs.filter (!projs.contains ·)
  let parentProjData := parentProjs.map fun nm =>
    {strName := nm, newName := nm}
  return projData ++ parentProjData

中文:
定义 mkParsedProjectionData
  签名: (structName : Name)
  定义体: do
  let env ← getEnv
  let projs := getStructureFields env structName
  if projs.size == 0 then
    throwError "Declaration {structName} is not a structure."
  let projData := projs.map fun fieldName => {
    strName := fieldName, newName := fieldName,
.isNone } isDefault := isSubobjectField? env structName fieldName
  let parentProjs := getStructureFieldsFlattened env structName false
  let parentProjs := parentProjs.filter (!projs.contains ·)
  let parentProjData := parentProjs.map fun nm =>
    {strName := nm, newName := nm}
  return projData ++ parentProjData
-/
def mkParsedProjectionData (structName : Name) : CoreM (Array ParsedProjectionData) := do
  let env ← getEnv
  let projs := getStructureFields env structName
  if projs.size == 0 then
    throwError "Declaration {structName} is not a structure."
  let projData := projs.map fun fieldName => {
    strName := fieldName, newName := fieldName,
.isNone } isDefault := isSubobjectField? env structName fieldName
  let parentProjs := getStructureFieldsFlattened env structName false
  let parentProjs := parentProjs.filter (!projs.contains ·)
  let parentProjData := parentProjs.map fun nm =>
    {strName := nm, newName := nm}
  return projData ++ parentProjData

/--
Definition of `applyProjectionRules` / `applyProjectionRules` 的定义

English:
definition applyProjectionRules
  signature: (projs : Array ParsedProjectionData) (rules : Array ProjectionRule)
  body: do
  let projs : Array ParsedProjectionData := rules.foldl (init := projs) fun projs rule =>
    match rule with
    | .rename strName strStx newName newStx =>
      if (projs.map (·.newName)).contains strName then
        projs.map fun proj => if proj.newName == strName then
          { proj with
            newName,
            newStx,
            strStx := if proj.strStx.isMissing then strStx else proj.strStx } else
          proj else
        projs.push {strName, strStx, newName, newStx}
    | .erase nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with
            isDefault := false,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx, isDefault := false}
    | .add nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with
            isDefault := true,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx}
    | .prefix nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with
            isPrefix := true,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx, isPrefix := true}
  trace[simps.debug] "Projection info after applying the rules: {projs}."
  unless (projs.map (·.newName)).toList.Nodup do throwError "\
    Invalid projection names. Two projections have the same name.\n\
    This is likely because a custom composition of projections was given the same name as an \
    existing projection. Solution: rename the existing projection (before naming the \
    custom projection)."
  pure projs

中文:
定义 applyProjectionRules
  签名: (projs : 数组 ParsedProjectionData) (rules : 数组 ProjectionRule)
  定义体: do
  let projs : Array ParsedProjectionData := rules.foldl (init := projs) fun projs rule =>
    match rule with
    | .rename strName strStx newName newStx =>
      if (projs.map (·.newName)).contains strName then
        projs.map fun proj => if proj.newName == strName then
          { proj with
            newName,
            newStx,
            strStx := if proj.strStx.isMissing then strStx else proj.strStx } else
          proj else
        projs.push {strName, strStx, newName, newStx}
    | .erase nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with
            isDefault := false,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx, isDefault := false}
    | .add nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with
            isDefault := true,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx}
    | .prefix nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with
            isPrefix := true,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx, isPrefix := true}
  trace[simps.debug] "Projection info after applying the rules: {projs}."
  unless (projs.map (·.newName)).toList.Nodup do throwError "\
    Invalid projection names. Two projections have the same name.\n\
    This is likely because a custom composition of projections was given the same name as an \
    existing projection. Solution: rename the existing projection (before naming the \
    custom projection)."
  pure projs
-/
def applyProjectionRules (projs : Array ParsedProjectionData) (rules : Array ProjectionRule) :
    CoreM (Array ParsedProjectionData) := do
  let projs : Array ParsedProjectionData := rules.foldl (init := projs) fun projs rule =>
    match rule with
    | .rename strName strStx newName newStx =>
      if (projs.map (·.newName)).contains strName then
        projs.map fun proj => if proj.newName == strName then
          { proj with
            newName,
            newStx,
            strStx := if proj.strStx.isMissing then strStx else proj.strStx } else
          proj else
        projs.push {strName, strStx, newName, newStx}
    | .erase nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with
            isDefault := false,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx, isDefault := false}
    | .add nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with
            isDefault := true,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx}
    | .prefix nm stx =>
      if (projs.map (·.newName)).contains nm then
        projs.map fun proj => if proj.newName = nm then
          { proj with
            isPrefix := true,
            strStx := if proj.strStx.isMissing then stx else proj.strStx } else
          proj else
        projs.push {strName := nm, newName := nm, strStx := stx, newStx := stx, isPrefix := true}
  trace[simps.debug] "Projection info after applying the rules: {projs}."
  unless (projs.map (·.newName)).toList.Nodup do throwError "\
    Invalid projection names. Two projections have the same name.\n\
    This is likely because a custom composition of projections was given the same name as an \
    existing projection. Solution: rename the existing projection (before naming the \
    custom projection)."
  pure projs

/--
Definition of `findProjection` / `findProjection` 的定义

English:
definition findProjection
  signature: (str : Name) (proj : ParsedProjectionData)
  body: do
  let env ← getEnv
let (rawExpr, nrs) ← MetaM.run'
    getCompositeOfProjections str proj.strName.lastComponentAsString
  if !proj.strStx.isMissing then
_ ← MetaM.run' TermElabM.run' addTermInfo proj.strStx rawExpr
  trace[simps.debug] "Projection {proj.newName} has default projection {rawExpr} and
    uses projection indices {nrs}"
  let customName := str ++ `Simps ++ proj.newName
  match env.find? customName with
  | some d@(.defnInfo _) =>
    let customProj := d.instantiateValueLevelParams! rawUnivs
    trace[simps.verbose] "found custom projection for {proj.newName}:{indentExpr customProj}"
    match (← MetaM.run' <| isDefEq customProj rawExpr) with
    | true =>
_ ← MetaM.run' TermElabM.run' addTermInfo proj.newStx
        ← mkConstWithLevelParams customName
      pure { proj with expr? := some customProj, projNrs := nrs, isCustom := true }
    | false =>
      -- if the type of the Expression is different, we show a different error message, because
      -- (in Lean 3) just stating that the expressions are different is quite unhelpful
      let customProjType ← MetaM.run' (inferType customProj)
      let rawExprType ← MetaM.run' (inferType rawExpr)
      if (← MetaM.run' (isDefEq customProjType rawExprType)) then
        throwError "Invalid custom projection:{indentExpr customProj}\n\
          Expression is not definitionally equal to {indentExpr rawExpr}"
      else
        throwError "Invalid custom projection:{indentExpr customProj}\n\
          Expression has different type than {str ++ proj.strName}. Given type:\
          {indentExpr customProjType}\nExpected type:{indentExpr rawExprType}\n\
          Note: make sure order of implicit arguments is exactly the same."
  | _ =>
_ ← MetaM.run' TermElabM.run' addTermInfo proj.newStx rawExpr
    pure {proj with expr? := some rawExpr, projNrs := nrs}

中文:
定义 findProjection
  签名: (str : Name) (proj : ParsedProjectionData)
  定义体: do
  let env ← getEnv
let (rawExpr, nrs) ← MetaM.run'
    getCompositeOfProjections str proj.strName.lastComponentAsString
  if !proj.strStx.isMissing then
_ ← MetaM.run' TermElabM.run' addTermInfo proj.strStx rawExpr
  trace[simps.debug] "Projection {proj.newName} has default projection {rawExpr} and
    uses projection indices {nrs}"
  let customName := str ++ `Simps ++ proj.newName
  match env.find? customName with
  | some d@(.defnInfo _) =>
    let customProj := d.instantiateValueLevelParams! rawUnivs
    trace[simps.verbose] "found custom projection for {proj.newName}:{indentExpr customProj}"
    match (← MetaM.run' <| isDefEq customProj rawExpr) with
    | true =>
_ ← MetaM.run' TermElabM.run' addTermInfo proj.newStx
        ← mkConstWithLevelParams customName
      pure { proj with expr? := some customProj, projNrs := nrs, isCustom := true }
    | false =>
      -- if the type of the Expression is different, we show a different error message, because
      -- (in Lean 3) just stating that the expressions are different is quite unhelpful
      let customProjType ← MetaM.run' (inferType customProj)
      let rawExprType ← MetaM.run' (inferType rawExpr)
      if (← MetaM.run' (isDefEq customProjType rawExprType)) then
        throwError "Invalid custom projection:{indentExpr customProj}\n\
          Expression is not definitionally equal to {indentExpr rawExpr}"
      else
        throwError "Invalid custom projection:{indentExpr customProj}\n\
          Expression has different type than {str ++ proj.strName}. Given type:\
          {indentExpr customProjType}\nExpected type:{indentExpr rawExprType}\n\
          Note: make sure order of implicit arguments is exactly the same."
  | _ =>
_ ← MetaM.run' TermElabM.run' addTermInfo proj.newStx rawExpr
    pure {proj with expr? := some rawExpr, projNrs := nrs}
-/
def findProjection (str : Name) (proj : ParsedProjectionData)
    (rawUnivs : List Level) : CoreM ParsedProjectionData := do
  let env ← getEnv
let (rawExpr, nrs) ← MetaM.run'
    getCompositeOfProjections str proj.strName.lastComponentAsString
  if !proj.strStx.isMissing then
_ ← MetaM.run' TermElabM.run' addTermInfo proj.strStx rawExpr
  trace[simps.debug] "Projection {proj.newName} has default projection {rawExpr} and
    uses projection indices {nrs}"
  let customName := str ++ `Simps ++ proj.newName
  match env.find? customName with
  | some d@(.defnInfo _) =>
    let customProj := d.instantiateValueLevelParams! rawUnivs
    trace[simps.verbose] "found custom projection for {proj.newName}:{indentExpr customProj}"
    match (← MetaM.run' <| isDefEq customProj rawExpr) with
    | true =>
_ ← MetaM.run' TermElabM.run' addTermInfo proj.newStx
        ← mkConstWithLevelParams customName
      pure { proj with expr? := some customProj, projNrs := nrs, isCustom := true }
    | false =>
      -- if the type of the Expression is different, we show a different error message, because
      -- (in Lean 3) just stating that the expressions are different is quite unhelpful
      let customProjType ← MetaM.run' (inferType customProj)
      let rawExprType ← MetaM.run' (inferType rawExpr)
      if (← MetaM.run' (isDefEq customProjType rawExprType)) then
        throwError "Invalid custom projection:{indentExpr customProj}\n\
          Expression is not definitionally equal to {indentExpr rawExpr}"
      else
        throwError "Invalid custom projection:{indentExpr customProj}\n\
          Expression has different type than {str ++ proj.strName}. Given type:\
          {indentExpr customProjType}\nExpected type:{indentExpr rawExprType}\n\
          Note: make sure order of implicit arguments is exactly the same."
  | _ =>
_ ← MetaM.run' TermElabM.run' addTermInfo proj.newStx rawExpr
    pure {proj with expr? := some rawExpr, projNrs := nrs}

/--
Definition of `checkForUnusedCustomProjs` / `checkForUnusedCustomProjs` 的定义

English:
definition checkForUnusedCustomProjs
  signature: (stx : Syntax) (str : Name) (projs : Array ParsedProjectionData)
  body: do
  let nrCustomProjections := projs.toList.countP (·.isCustom)
  let env ← getEnv
  let customDeclarations := env.constants.map₂.foldl (init := #[]) fun xs nm _ =>
    if (str ++ `Simps).isPrefixOf nm && !nm.isInternalDetail && !isReservedName env nm then
      xs.push nm
    else
      xs
  if nrCustomProjections < customDeclarations.size then
    Linter.logLintIf linter.simpsUnusedCustomDeclarations stx m!"\
      Not all of the custom declarations {customDeclarations} are used. Double check the \
      spelling, and use `?` to get more information."

中文:
定义 checkForUnusedCustomProjs
  签名: (stx : Syntax) (str : Name) (projs : 数组 ParsedProjectionData)
  定义体: do
  let nrCustomProjections := projs.toList.countP (·.isCustom)
  let env ← getEnv
  let customDeclarations := env.constants.map₂.foldl (init := #[]) fun xs nm _ =>
    if (str ++ `Simps).isPrefixOf nm && !nm.isInternalDetail && !isReservedName env nm then
      xs.push nm
    else
      xs
  if nrCustomProjections < customDeclarations.size then
    Linter.logLintIf linter.simpsUnusedCustomDeclarations stx m!"\
      Not all of the custom declarations {customDeclarations} are used. Double check the \
      spelling, and use `?` to get more information."
-/
def checkForUnusedCustomProjs (stx : Syntax) (str : Name) (projs : Array ParsedProjectionData) :
    CoreM Unit := do
  let nrCustomProjections := projs.toList.countP (·.isCustom)
  let env ← getEnv
  let customDeclarations := env.constants.map₂.foldl (init := #[]) fun xs nm _ =>
    if (str ++ `Simps).isPrefixOf nm && !nm.isInternalDetail && !isReservedName env nm then
      xs.push nm
    else
      xs
  if nrCustomProjections < customDeclarations.size then
    Linter.logLintIf linter.simpsUnusedCustomDeclarations stx m!"\
      Not all of the custom declarations {customDeclarations} are used. Double check the \
      spelling, and use `?` to get more information."

/--
Definition of `findAutomaticProjectionsAux` / `findAutomaticProjectionsAux` 的定义

English:
definition findAutomaticProjectionsAux
  signature: (str : Name) (proj : ParsedProjectionData) (args : Array Expr)
  body: do
  if let some ⟨className, isNotation, findArgs⟩ :=
    notationClassAttr.find? (← getEnv) proj.strName then
    let findArgs ← unsafe evalConst findArgType findArgs
    let classArgs ← try findArgs str className args
    catch ex =>
      trace[simps.debug] "Projection {proj.strName} is likely unrelated to the projection of \
        {className}:\n{ex.toMessageData}"
      return none
    let classArgs ← classArgs.mapM fun e => match e with
      | none => mkFreshExprMVar none
      | some e => pure e
    let classArgs := classArgs.map Arg.expr
    let projName := (getStructureFields (← getEnv) className)[0]!
    let projName := className ++ projName
    let eStr := mkAppN (← mkConstWithLevelParams str) args
    let eInstType ←
      try withoutErrToSorry (elabAppArgs (← Term.mkConst className) #[] classArgs none true false)
      catch ex =>
        trace[simps.debug] "Projection doesn't have the right type for the automatic projection:\n\
          {ex.toMessageData}"
        return none
    return ← withLocalDeclD `self eStr fun instStr => do
      trace[simps.debug] "found projection {proj.strName}. Trying to synthesize {eInstType}."
      let eInst ← try synthInstance eInstType
      catch ex =>
        trace[simps.debug] "Didn't find instance:\n{ex.toMessageData}"
        return none
      let projExpr ← elabAppArgs (← Term.mkConst projName) #[] (classArgs.push <| .expr eInst)
        none true false
      let projExpr ← mkLambdaFVars (if isNotation then args.push instStr else args) projExpr
      let projExpr ← instantiateMVars projExpr
      return (projExpr, projName)
  return none

中文:
定义 findAutomaticProjectionsAux
  签名: (str : Name) (proj : ParsedProjectionData) (args : 数组 Expr)
  定义体: do
  if let some ⟨className, isNotation, findArgs⟩ :=
    notationClassAttr.find? (← getEnv) proj.strName then
    let findArgs ← unsafe evalConst findArgType findArgs
    let classArgs ← try findArgs str className args
    catch ex =>
      trace[simps.debug] "Projection {proj.strName} is likely unrelated to the projection of \
        {className}:\n{ex.toMessageData}"
      return none
    let classArgs ← classArgs.mapM fun e => match e with
      | none => mkFreshExprMVar none
      | some e => pure e
    let classArgs := classArgs.map Arg.expr
    let projName := (getStructureFields (← getEnv) className)[0]!
    let projName := className ++ projName
    let eStr := mkAppN (← mkConstWithLevelParams str) args
    let eInstType ←
      try withoutErrToSorry (elabAppArgs (← Term.mkConst className) #[] classArgs none true false)
      catch ex =>
        trace[simps.debug] "Projection doesn't have the right type for the automatic projection:\n\
          {ex.toMessageData}"
        return none
    return ← withLocalDeclD `self eStr fun instStr => do
      trace[simps.debug] "found projection {proj.strName}. Trying to synthesize {eInstType}."
      let eInst ← try synthInstance eInstType
      catch ex =>
        trace[simps.debug] "Didn't find instance:\n{ex.toMessageData}"
        return none
      let projExpr ← elabAppArgs (← Term.mkConst projName) #[] (classArgs.push <| .expr eInst)
        none true false
      let projExpr ← mkLambdaFVars (if isNotation then args.push instStr else args) projExpr
      let projExpr ← instantiateMVars projExpr
      return (projExpr, projName)
  return none
-/
def findAutomaticProjectionsAux (str : Name) (proj : ParsedProjectionData) (args : Array Expr) :
TermElabM Option (Expr × Name) := do
  if let some ⟨className, isNotation, findArgs⟩ :=
    notationClassAttr.find? (← getEnv) proj.strName then
    let findArgs ← unsafe evalConst findArgType findArgs
    let classArgs ← try findArgs str className args
    catch ex =>
      trace[simps.debug] "Projection {proj.strName} is likely unrelated to the projection of \
        {className}:\n{ex.toMessageData}"
      return none
    let classArgs ← classArgs.mapM fun e => match e with
      | none => mkFreshExprMVar none
      | some e => pure e
    let classArgs := classArgs.map Arg.expr
    let projName := (getStructureFields (← getEnv) className)[0]!
    let projName := className ++ projName
    let eStr := mkAppN (← mkConstWithLevelParams str) args
    let eInstType ←
      try withoutErrToSorry (elabAppArgs (← Term.mkConst className) #[] classArgs none true false)
      catch ex =>
        trace[simps.debug] "Projection doesn't have the right type for the automatic projection:\n\
          {ex.toMessageData}"
        return none
    return ← withLocalDeclD `self eStr fun instStr => do
      trace[simps.debug] "found projection {proj.strName}. Trying to synthesize {eInstType}."
      let eInst ← try synthInstance eInstType
      catch ex =>
        trace[simps.debug] "Didn't find instance:\n{ex.toMessageData}"
        return none
      let projExpr ← elabAppArgs (← Term.mkConst projName) #[] (classArgs.push <| .expr eInst)
        none true false
      let projExpr ← mkLambdaFVars (if isNotation then args.push instStr else args) projExpr
      let projExpr ← instantiateMVars projExpr
      return (projExpr, projName)
  return none

/--
Definition of `findAutomaticProjections` / `findAutomaticProjections` 的定义

English:
definition findAutomaticProjections
  signature: (str : Name) (projs : Array ParsedProjectionData)
  body: do
  let strDecl ← getConstInfo str
  trace[simps.debug] "debug: {projs}"
MetaM.run' TermElabM.run' (s := {levelNames := strDecl.levelParams})
  forallTelescope strDecl.type fun args _ => do
  let projs ← projs.mapM fun proj => do
    if let some (projExpr, projName) ← findAutomaticProjectionsAux str proj args then
      unless ← isDefEq projExpr proj.expr?.get! do
        throwError "The projection {proj.newName} is not definitionally equal to an application \
          of {projName}:{indentExpr proj.expr?.get!}\nvs{indentExpr projExpr}"
      if proj.isCustom then
        trace[simps.verbose] "Warning: Projection {proj.newName} is given manually by the user, \
          but it can be generated automatically."
        return proj
      trace[simps.verbose] "Using {indentExpr projExpr}\nfor projection {proj.newName}."
      return { proj with expr? := some projExpr }
    return proj
  return projs

中文:
定义 findAutomaticProjections
  签名: (str : Name) (projs : 数组 ParsedProjectionData)
  定义体: do
  let strDecl ← getConstInfo str
  trace[simps.debug] "debug: {projs}"
MetaM.run' TermElabM.run' (s := {levelNames := strDecl.levelParams})
  forallTelescope strDecl.type fun args _ => do
  let projs ← projs.mapM fun proj => do
    if let some (projExpr, projName) ← findAutomaticProjectionsAux str proj args then
      unless ← isDefEq projExpr proj.expr?.get! do
        throwError "The projection {proj.newName} is not definitionally equal to an application \
          of {projName}:{indentExpr proj.expr?.get!}\nvs{indentExpr projExpr}"
      if proj.isCustom then
        trace[simps.verbose] "Warning: Projection {proj.newName} is given manually by the user, \
          but it can be generated automatically."
        return proj
      trace[simps.verbose] "Using {indentExpr projExpr}\nfor projection {proj.newName}."
      return { proj with expr? := some projExpr }
    return proj
  return projs
-/
def findAutomaticProjections (str : Name) (projs : Array ParsedProjectionData) :
    CoreM (Array ParsedProjectionData) := do
  let strDecl ← getConstInfo str
  trace[simps.debug] "debug: {projs}"
MetaM.run' TermElabM.run' (s := {levelNames := strDecl.levelParams})
  forallTelescope strDecl.type fun args _ => do
  let projs ← projs.mapM fun proj => do
    if let some (projExpr, projName) ← findAutomaticProjectionsAux str proj args then
      unless ← isDefEq projExpr proj.expr?.get! do
        throwError "The projection {proj.newName} is not definitionally equal to an application \
          of {projName}:{indentExpr proj.expr?.get!}\nvs{indentExpr projExpr}"
      if proj.isCustom then
        trace[simps.verbose] "Warning: Projection {proj.newName} is given manually by the user, \
          but it can be generated automatically."
        return proj
      trace[simps.verbose] "Using {indentExpr projExpr}\nfor projection {proj.newName}."
      return { proj with expr? := some projExpr }
    return proj
  return projs

/--
Definition of `getRawProjections` / `getRawProjections` 的定义

English:
definition getRawProjections
  signature: (stx : Syntax) (str : Name) (traceIfExists : Bool := false)
  body: do
  withOptions (fun o => if trc then o.set `trace.simps.verbose true else o) do
  let env ← getEnv
  if let some data := structureExt.find? env str then
    -- We always print the projections when they already exists and are called by
    -- `initialize_simps_projections`.
    withOptions (fun o => if traceIfExists then o.set `trace.simps.verbose true else o) do
      trace[simps.verbose]
        projectionsInfo data.2.toList "The projections for this structure have already been \
        initialized by a previous invocation of `initialize_simps_projections` or `@[simps]`.\n\
        Generated projections for" str
    return data
  trace[simps.verbose] "generating projection information for structure {str}."
  trace[simps.debug] "Applying the rules {rules}."
  let strDecl ← getConstInfo str
  let rawLevels := strDecl.levelParams
  let rawUnivs := rawLevels.map Level.param
  let projs ← mkParsedProjectionData str
  let projs ← applyProjectionRules projs rules
  let projs ← projs.mapM fun proj => findProjection str proj rawUnivs
  checkForUnusedCustomProjs stx str projs
  let projs ← findAutomaticProjections str projs
  let projs := projs.map (·.toProjectionData)
  -- make all proofs non-default.
  let projs ← projs.mapM fun proj => do
    match (← MetaM.run' <| isProof proj.expr) with
    | true => pure { proj with isDefault := false }
    | false => pure proj
  trace[simps.verbose] projectionsInfo projs.toList "generated projections for" str
  structureExt.add str (rawLevels, projs)
  trace[simps.debug] "Generated raw projection data:{indentD <| toMessageData (rawLevels, projs)}"
  pure (rawLevels, projs)

library_note «custom simps projection» /--
You can specify custom projections for the `@[simps]` attribute.
To do this for the projection `MyStructure.originalProjection` by adding a declaration
`MyStructure.Simps.myProjection` that is definitionally equal to
`MyStructure.originalProjection` but has the projection in the desired (simp-normal) form.
Then you can call
```
initialize_simps_projections (originalProjection → myProjection, ...)
```
to register this projection. See `elabInitializeSimpsProjections` for more information.

You can also specify custom projections that are definitionally equal to a composite of multiple
projections. This is often desirable when extending structures (without `oldStructureCmd`).

`CoeFun` and notation class (like `Mul`) instances will be automatically used, if they
are definitionally equal to a projection of the structure (but not when they are equal to the
composite of multiple projections).
-/

中文:
定义 getRawProjections
  签名: (stx : Syntax) (str : Name) (traceIfExists : 布尔值 := false)
  定义体: do
  withOptions (fun o => if trc then o.set `trace.simps.verbose true else o) do
  let env ← getEnv
  if let some data := structureExt.find? env str then
    -- We always print the projections when they already exists and are called by
    -- `initialize_simps_projections`.
    withOptions (fun o => if traceIfExists then o.set `trace.simps.verbose true else o) do
      trace[simps.verbose]
        projectionsInfo data.2.toList "The projections for this structure have already been \
        initialized by a previous invocation of `initialize_simps_projections` or `@[simps]`.\n\
        Generated projections for" str
    return data
  trace[simps.verbose] "generating projection information for structure {str}."
  trace[simps.debug] "Applying the rules {rules}."
  let strDecl ← getConstInfo str
  let rawLevels := strDecl.levelParams
  let rawUnivs := rawLevels.map Level.param
  let projs ← mkParsedProjectionData str
  let projs ← applyProjectionRules projs rules
  let projs ← projs.mapM fun proj => findProjection str proj rawUnivs
  checkForUnusedCustomProjs stx str projs
  let projs ← findAutomaticProjections str projs
  let projs := projs.map (·.toProjectionData)
  -- make all proofs non-default.
  let projs ← projs.mapM fun proj => do
    match (← MetaM.run' <| isProof proj.expr) with
    | true => pure { proj with isDefault := false }
    | false => pure proj
  trace[simps.verbose] projectionsInfo projs.toList "generated projections for" str
  structureExt.add str (rawLevels, projs)
  trace[simps.debug] "Generated raw projection data:{indentD <| toMessageData (rawLevels, projs)}"
  pure (rawLevels, projs)

library_note «custom simps projection» /--
You can specify custom projections for the `@[simps]` attribute.
To do this for the projection `MyStructure.originalProjection` by adding a declaration
`MyStructure.Simps.myProjection` that is definitionally equal to
`MyStructure.originalProjection` but has the projection in the desired (simp-normal) form.
Then you can call
```
initialize_simps_projections (originalProjection → myProjection, ...)
```
to register this projection. See `elabInitializeSimpsProjections` for more information.

You can also specify custom projections that are definitionally equal to a composite of multiple
projections. This is often desirable when extending structures (without `oldStructureCmd`).

`CoeFun` and notation class (like `Mul`) instances will be automatically used, if they
are definitionally equal to a projection of the structure (but not when they are equal to the
composite of multiple projections).
-/
-/
def getRawProjections (stx : Syntax) (str : Name) (traceIfExists : Bool := false)
    (rules : Array ProjectionRule := #[]) (trc := false) :
    CoreM (List Name × Array ProjectionData) := do
  withOptions (fun o => if trc then o.set `trace.simps.verbose true else o) do
  let env ← getEnv
  if let some data := structureExt.find? env str then
    -- We always print the projections when they already exists and are called by
    -- `initialize_simps_projections`.
    withOptions (fun o => if traceIfExists then o.set `trace.simps.verbose true else o) do
      trace[simps.verbose]
        projectionsInfo data.2.toList "The projections for this structure have already been \
        initialized by a previous invocation of `initialize_simps_projections` or `@[simps]`.\n\
        Generated projections for" str
    return data
  trace[simps.verbose] "generating projection information for structure {str}."
  trace[simps.debug] "Applying the rules {rules}."
  let strDecl ← getConstInfo str
  let rawLevels := strDecl.levelParams
  let rawUnivs := rawLevels.map Level.param
  let projs ← mkParsedProjectionData str
  let projs ← applyProjectionRules projs rules
  let projs ← projs.mapM fun proj => findProjection str proj rawUnivs
  checkForUnusedCustomProjs stx str projs
  let projs ← findAutomaticProjections str projs
  let projs := projs.map (·.toProjectionData)
  -- make all proofs non-default.
  let projs ← projs.mapM fun proj => do
    match (← MetaM.run' <| isProof proj.expr) with
    | true => pure { proj with isDefault := false }
    | false => pure proj
  trace[simps.verbose] projectionsInfo projs.toList "generated projections for" str
  structureExt.add str (rawLevels, projs)
  trace[simps.debug] "Generated raw projection data:{indentD <| toMessageData (rawLevels, projs)}"
  pure (rawLevels, projs)

library_note «custom simps projection» /--
You can specify custom projections for the `@[simps]` attribute.
To do this for the projection `MyStructure.originalProjection` by adding a declaration
`MyStructure.Simps.myProjection` that is definitionally equal to
`MyStructure.originalProjection` but has the projection in the desired (simp-normal) form.
Then you can call
```
initialize_simps_projections (originalProjection → myProjection, ...)
```
to register this projection. See `elabInitializeSimpsProjections` for more information.

You can also specify custom projections that are definitionally equal to a composite of multiple
projections. This is often desirable when extending structures (without `oldStructureCmd`).

`CoeFun` and notation class (like `Mul`) instances will be automatically used, if they
are definitionally equal to a projection of the structure (but not when they are equal to the
composite of multiple projections).
-/

/--
Definition of `elabSimpsRule` / `elabSimpsRule` 的定义

English:
definition elabSimpsRule
  signature: : Syntax -> CommandElabM ProjectionRule

中文:
定义 elabSimpsRule
  签名: : Syntax -> CommandElabM ProjectionRule
-/
def elabSimpsRule : Syntax -> CommandElabM ProjectionRule
  | `(simpsRule| $id1 -> $id2) => return .rename id1.getId id1.raw id2.getId id2.raw
  | `(simpsRule| - $id) => return .erase id.getId id.raw
  | `(simpsRule| + $id) => return .add id.getId id.raw
  | `(simpsRule| as_prefix $id) => return .prefix id.getId id.raw
  | _ => Elab.throwUnsupportedSyntax

/--
Definition of `elabInitializeSimpsProjections` / `elabInitializeSimpsProjections` 的定义

English:
definition elabInitializeSimpsProjections
  signature: : CommandElab
  body: stxs.getD .mk #[]
    let rules ← stxs.getElems.raw.mapM elabSimpsRule
    let nm ← resolveGlobalConstNoOverload id
_ ← liftTermElabM addTermInfo id.raw ← mkConstWithLevelParams nm
_ ← liftCoreM getRawProjections stx nm true rules trc.isSome
  | _ => throwUnsupportedSyntax

中文:
定义 elabInitializeSimpsProjections
  签名: : CommandElab
  定义体: stxs.getD .mk #[]
    let rules ← stxs.getElems.raw.mapM elabSimpsRule
    let nm ← resolveGlobalConstNoOverload id
_ ← liftTermElabM addTermInfo id.raw ← mkConstWithLevelParams nm
_ ← liftCoreM getRawProjections stx nm true rules trc.isSome
  | _ => throwUnsupportedSyntax
-/
@[command_elab «initialize_simps_projections»] def elabInitializeSimpsProjections : CommandElab
  | stx@`(initialize_simps_projections $[?%$trc]? $id $[($stxs,*)]?) => do
let stxs := stxs.getD .mk #[]
    let rules ← stxs.getElems.raw.mapM elabSimpsRule
    let nm ← resolveGlobalConstNoOverload id
_ ← liftTermElabM addTermInfo id.raw ← mkConstWithLevelParams nm
_ ← liftCoreM getRawProjections stx nm true rules trc.isSome
  | _ => throwUnsupportedSyntax

/--
Definition of `Config` / `Config` 的定义

English:
structure Config
  parameters: where
  axioms and operations (10):
    - isSimp : = true
    - attrs : Array Attribute  [default: #[]]
    - simpRhs : = false
    - dsimpLhs : = false
    - typeMd : = TransparencyMode.instances
    - rhsMd : = TransparencyMode.reducible
    - fullyApplied : = true
    - notRecursive : = [`Prod, `PProd, `Opposite, `PreOpposite]
    - debug : = false
    - nameStem : Option String  [default: none]

中文:
结构 余nfig
  参数: where
  公理与运算 (10 个):
    - isSimp : = true
    - attrs : 数组 Attribute  [默认: #[]]
    - simpRhs : = false
    - dsimpLhs : = false
    - typeMd : = TransparencyMode.instances
    - rhsMd : = TransparencyMode.reducible
    - fullyApplied : = true
    - notRecursive : = [`积类型, `命题积类型, `对偶, `PreOpposite]
    - debug : = false
    - nameStem : 选项类型 String  [默认: none]
-/
structure Config where
  /-- Make generated lemmas simp lemmas -/
  isSimp := true
  /-- Other attributes to apply to generated lemmas. -/
  attrs : Array Attribute := #[]
  /-- simplify the right-hand side of generated simp-lemmas using `dsimp, simp`. -/
  simpRhs := false
  /-- simplify the left-hand side of the generated lemmas using `dsimp`. -/
  dsimpLhs := false
  /-- TransparencyMode used to reduce the type in order to detect whether it is a structure. -/
  typeMd := TransparencyMode.instances
  /-- TransparencyMode used to reduce the right-hand side in order to detect whether it is a
  constructor. Note: was `none` in Lean 3 -/
  rhsMd := TransparencyMode.reducible
  /-- Generated lemmas that are fully applied, i.e. generates equalities between applied functions.
  Set this to `false` to generate equalities between functions. -/
  fullyApplied := true
  /-- List of types in which we are not recursing to generate simplification lemmas.
  E.g. if we write `@[simps] def e : α × β ≃ β × α := ...` we will generate `e_apply` and not
  `e_apply_fst`. -/
  notRecursive := [`Prod, `PProd, `Opposite, `PreOpposite]
  /-- Output debug messages. Not used much, use `set_option simps.debug true` instead. -/
  debug := false
  /-- The stem to use for the projection names. If `none`, the default, use the suffix of the
  current declaration name, or the empty string if the declaration is an instance and the instance
  is named according to the `inst` convention. -/
  nameStem : Option String := none
  deriving Inhabited

/-- Function elaborating `Config`. -/
declare_core_config_elab elabSimpsConfig Config where
  omit attrs
  option attr := fun cfg item => do
    item.addConstInfo ``Config.attrs
    match item.ref with
    | `(Attr.simpsConfigAttrItem| (attr := $[$attrs],*)) =>
      let extraAttrs ← elabAttrs attrs
      return { cfg with attrs := cfg.attrs ++ extraAttrs }
    | _ =>
      throwErrorAt item.value "Expecting a list of one or more attributes."

/--
Definition of `_root_.Lean.Expr.instantiateLambdasOrApps` / `_root_.Lean.Expr.instantiateLambdasOrApps` 的定义

English:
definition _root_.Lean.Expr.instantiateLambdasOrApps
  signature: (es : Array Expr) (e : Expr)
  body: e.betaRev es.reverse true -- check if this is what I want

中文:
定义 _root_.Lean.Expr.instantiateLambdasOrApps
  签名: (es : 数组 Expr) (e : Expr)
  定义体: e.betaRev es.reverse true -- check if this is what I want
-/
partial def _root_.Lean.Expr.instantiateLambdasOrApps (es : Array Expr) (e : Expr) : Expr :=
  e.betaRev es.reverse true -- check if this is what I want

/--
Definition of `getProjectionExprs` / `getProjectionExprs` 的定义

English:
definition getProjectionExprs
  signature: (stx : Syntax) (tgt : Expr) (rhs : Expr) (cfg : Config)
  body: do
  -- the parameters of the structure
  let params := tgt.getAppArgs
  if cfg.debug && !(← (params.zip rhs.getAppArgs).allM fun ⟨a, b⟩ => isDefEq a b) then
    throwError "unreachable code: parameters are not definitionally equal"
  let str := tgt.getAppFn.constName?.getD default
  -- the fields of the object
  let rhsArgs := rhs.getAppArgs.toList.drop params.size
  let (rawUnivs, projDeclata) ← getRawProjections stx str
  projDeclata.mapM fun proj => do
    let expr := proj.expr.instantiateLevelParams rawUnivs tgt.getAppFn.constLevels!
    -- after instantiating universes, we have to check again whether the expression is a proof.
    let proj := if ← isProof expr
      then { proj with isDefault := false }
      else proj
    return (rhsArgs.getD (fallback := default) proj.projNrs.head!,
      { proj with
        expr := expr.instantiateLambdasOrApps params
        projNrs := proj.projNrs.tail })

中文:
定义 getProjectionExprs
  签名: (stx : Syntax) (tgt : Expr) (rhs : Expr) (cfg : 余nfig)
  定义体: do
  -- the parameters of the structure
  let params := tgt.getAppArgs
  if cfg.debug && !(← (params.zip rhs.getAppArgs).allM fun ⟨a, b⟩ => isDefEq a b) then
    throwError "unreachable code: parameters are not definitionally equal"
  let str := tgt.getAppFn.constName?.getD default
  -- the fields of the object
  let rhsArgs := rhs.getAppArgs.toList.drop params.size
  let (rawUnivs, projDeclata) ← getRawProjections stx str
  projDeclata.mapM fun proj => do
    let expr := proj.expr.instantiateLevelParams rawUnivs tgt.getAppFn.constLevels!
    -- after instantiating universes, we have to check again whether the expression is a proof.
    let proj := if ← isProof expr
      then { proj with isDefault := false }
      else proj
    return (rhsArgs.getD (fallback := default) proj.projNrs.head!,
      { proj with
        expr := expr.instantiateLambdasOrApps params
        projNrs := proj.projNrs.tail })
-/
def getProjectionExprs (stx : Syntax) (tgt : Expr) (rhs : Expr) (cfg : Config) :
MetaM Array Expr × ProjectionData := do
  -- the parameters of the structure
  let params := tgt.getAppArgs
  if cfg.debug && !(← (params.zip rhs.getAppArgs).allM fun ⟨a, b⟩ => isDefEq a b) then
    throwError "unreachable code: parameters are not definitionally equal"
  let str := tgt.getAppFn.constName?.getD default
  -- the fields of the object
  let rhsArgs := rhs.getAppArgs.toList.drop params.size
  let (rawUnivs, projDeclata) ← getRawProjections stx str
  projDeclata.mapM fun proj => do
    let expr := proj.expr.instantiateLevelParams rawUnivs tgt.getAppFn.constLevels!
    -- after instantiating universes, we have to check again whether the expression is a proof.
    let proj := if ← isProof expr
      then { proj with isDefault := false }
      else proj
    return (rhsArgs.getD (fallback := default) proj.projNrs.head!,
      { proj with
        expr := expr.instantiateLambdasOrApps params
        projNrs := proj.projNrs.tail })

variable (ref : Syntax) (univs : List Name)

/--
Definition of `addProjection` / `addProjection` 的定义

English:
definition addProjection
  signature: (declName : Name) (type lhs rhs : Expr) (args : Array Expr)
  body: -- Enable `backward.defeqAttrib.useBackward` so the dsimp/simp normalization
  -- below still uses `@[backward_defeq]`-only theorems (which would have been
  -- `@[defeq]` under the pre-stricter-inference rules). Without this, rfl-shaped
  -- projections end up with compound (non-rfl) proofs, which prevents
  -- `inferDefEqAttr` from tagging them, which cascades through downstream
  -- `@[simps!]` invocations.
  withOptions (fun opts => backward.defeqAttrib.useBackward.set opts true) do
  trace[simps.debug] "Planning to add the equality{indentD m!"{lhs} = ({rhs} : {type})"}"
  let env ← getEnv
  -- simplify `rhs` if `cfg.simpRhs` is true
  let lvl ← getLevel type
  let mut (rhs, prf) := (rhs, mkAppN (mkConst `Eq.refl [lvl]) #[type, lhs])
  if cfg.simpRhs then
    let ctx ← mkSimpContext
    let (rhs2, _) ← dsimp rhs ctx
    if rhs != rhs2 then
      trace[simps.debug] "`dsimp` simplified rhs to{indentExpr rhs2}"
    else
      trace[simps.debug] "`dsimp` failed to simplify rhs"
    let (result, _) ← simp rhs2 ctx
    if rhs2 != result.expr then
      trace[simps.debug] "`simp` simplified rhs to{indentExpr result.expr}"
    else
      trace[simps.debug] "`simp` failed to simplify rhs"
    rhs := result.expr
    prf := result.proof?.getD prf
  -- dsimplify `lhs` if `cfg.dsimpLhs` is true
  let mut lhs := lhs
  if cfg.dsimpLhs then
    let ctx ← mkSimpContext
    (lhs, _) ← dsimp lhs ctx
  let eqAp := mkApp3 (mkConst `Eq [lvl]) type lhs rhs
  let declType ← mkForallFVars args eqAp
  let declValue ← mkLambdaFVars args prf
  if (env.find? declName).isSome then -- diverging behavior from Lean 3
    throwError "simps tried to add lemma{indentD m!"{.ofConstName declName} : {declType}"}\n\
      to the environment, but it already exists."
  trace[simps.verbose] "adding projection {declName}:{indentExpr declType}"
  Mathlib.Tactic.warnIfImplicitIllTyped ref declName declType
  prependError "Failed to add projection lemma {declName}:" do
addDecl .thmDecl {
      name := declName
      levelParams := univs
      type := declType
      value := declValue }
  inferDefEqAttr declName
  -- add term info and apply attributes
  addDeclarationRangesFromSyntax declName (← getRef) ref
.run' addTermInfo' ref (← mkConstWithLevelParams declName) (isBinder := true)
  if cfg.isSimp then
addSimpTheorem simpExtension declName true false .global eval_prio default
  TermElabM.run' do
    Elab.Term.applyAttributes declName cfg.attrs

中文:
定义 addProjection
  签名: (declName : Name) (type lhs rhs : Expr) (args : 数组 Expr)
  定义体: -- Enable `backward.defeqAttrib.useBackward` so the dsimp/simp normalization
  -- below still uses `@[backward_defeq]`-only theorems (which would have been
  -- `@[defeq]` under the pre-stricter-inference rules). Without this, rfl-shaped
  -- projections end up with compound (non-rfl) proofs, which prevents
  -- `inferDefEqAttr` from tagging them, which cascades through downstream
  -- `@[simps!]` invocations.
  withOptions (fun opts => backward.defeqAttrib.useBackward.set opts true) do
  trace[simps.debug] "Planning to add the equality{indentD m!"{lhs} = ({rhs} : {type})"}"
  let env ← getEnv
  -- simplify `rhs` if `cfg.simpRhs` is true
  let lvl ← getLevel type
  let mut (rhs, prf) := (rhs, mkAppN (mkConst `Eq.refl [lvl]) #[type, lhs])
  if cfg.simpRhs then
    let ctx ← mkSimpContext
    let (rhs2, _) ← dsimp rhs ctx
    if rhs != rhs2 then
      trace[simps.debug] "`dsimp` simplified rhs to{indentExpr rhs2}"
    else
      trace[simps.debug] "`dsimp` failed to simplify rhs"
    let (result, _) ← simp rhs2 ctx
    if rhs2 != result.expr then
      trace[simps.debug] "`simp` simplified rhs to{indentExpr result.expr}"
    else
      trace[simps.debug] "`simp` failed to simplify rhs"
    rhs := result.expr
    prf := result.proof?.getD prf
  -- dsimplify `lhs` if `cfg.dsimpLhs` is true
  let mut lhs := lhs
  if cfg.dsimpLhs then
    let ctx ← mkSimpContext
    (lhs, _) ← dsimp lhs ctx
  let eqAp := mkApp3 (mkConst `Eq [lvl]) type lhs rhs
  let declType ← mkForallFVars args eqAp
  let declValue ← mkLambdaFVars args prf
  if (env.find? declName).isSome then -- diverging behavior from Lean 3
    throwError "simps tried to add lemma{indentD m!"{.ofConstName declName} : {declType}"}\n\
      to the environment, but it already exists."
  trace[simps.verbose] "adding projection {declName}:{indentExpr declType}"
  Mathlib.Tactic.warnIfImplicitIllTyped ref declName declType
  prependError "Failed to add projection lemma {declName}:" do
addDecl .thmDecl {
      name := declName
      levelParams := univs
      type := declType
      value := declValue }
  inferDefEqAttr declName
  -- add term info and apply attributes
  addDeclarationRangesFromSyntax declName (← getRef) ref
.run' addTermInfo' ref (← mkConstWithLevelParams declName) (isBinder := true)
  if cfg.isSimp then
addSimpTheorem simpExtension declName true false .global eval_prio default
  TermElabM.run' do
    Elab.Term.applyAttributes declName cfg.attrs
-/
def addProjection (declName : Name) (type lhs rhs : Expr) (args : Array Expr)
    (cfg : Config) : MetaM Unit :=
  -- Enable `backward.defeqAttrib.useBackward` so the dsimp/simp normalization
  -- below still uses `@[backward_defeq]`-only theorems (which would have been
  -- `@[defeq]` under the pre-stricter-inference rules). Without this, rfl-shaped
  -- projections end up with compound (non-rfl) proofs, which prevents
  -- `inferDefEqAttr` from tagging them, which cascades through downstream
  -- `@[simps!]` invocations.
  withOptions (fun opts => backward.defeqAttrib.useBackward.set opts true) do
  trace[simps.debug] "Planning to add the equality{indentD m!"{lhs} = ({rhs} : {type})"}"
  let env ← getEnv
  -- simplify `rhs` if `cfg.simpRhs` is true
  let lvl ← getLevel type
  let mut (rhs, prf) := (rhs, mkAppN (mkConst `Eq.refl [lvl]) #[type, lhs])
  if cfg.simpRhs then
    let ctx ← mkSimpContext
    let (rhs2, _) ← dsimp rhs ctx
    if rhs != rhs2 then
      trace[simps.debug] "`dsimp` simplified rhs to{indentExpr rhs2}"
    else
      trace[simps.debug] "`dsimp` failed to simplify rhs"
    let (result, _) ← simp rhs2 ctx
    if rhs2 != result.expr then
      trace[simps.debug] "`simp` simplified rhs to{indentExpr result.expr}"
    else
      trace[simps.debug] "`simp` failed to simplify rhs"
    rhs := result.expr
    prf := result.proof?.getD prf
  -- dsimplify `lhs` if `cfg.dsimpLhs` is true
  let mut lhs := lhs
  if cfg.dsimpLhs then
    let ctx ← mkSimpContext
    (lhs, _) ← dsimp lhs ctx
  let eqAp := mkApp3 (mkConst `Eq [lvl]) type lhs rhs
  let declType ← mkForallFVars args eqAp
  let declValue ← mkLambdaFVars args prf
  if (env.find? declName).isSome then -- diverging behavior from Lean 3
    throwError "simps tried to add lemma{indentD m!"{.ofConstName declName} : {declType}"}\n\
      to the environment, but it already exists."
  trace[simps.verbose] "adding projection {declName}:{indentExpr declType}"
  Mathlib.Tactic.warnIfImplicitIllTyped ref declName declType
  prependError "Failed to add projection lemma {declName}:" do
addDecl .thmDecl {
      name := declName
      levelParams := univs
      type := declType
      value := declValue }
  inferDefEqAttr declName
  -- add term info and apply attributes
  addDeclarationRangesFromSyntax declName (← getRef) ref
.run' addTermInfo' ref (← mkConstWithLevelParams declName) (isBinder := true)
  if cfg.isSimp then
addSimpTheorem simpExtension declName true false .global eval_prio default
  TermElabM.run' do
    Elab.Term.applyAttributes declName cfg.attrs

/--
Definition of `headStructureEtaReduce` / `headStructureEtaReduce` 的定义

English:
definition headStructureEtaReduce
  signature: (e : Expr)
  body: do
  let env ← getEnv
  let (ctor, args) := e.getAppFnArgs
  let some (.ctorInfo { induct := struct, numParams, ..}) := env.find? ctor | pure e
  let some { fieldNames, .. } := getStructureInfo? env struct | pure e
  let (params, fields) := args.toList.splitAt numParams -- fix if `Array.take` / `Array.drop` exist
  trace[simps.debug]
    "rhs is constructor application with params{indentD params}\nand fields {indentD fields}"
  let field0 :: fieldsTail := fields | return e
  let fieldName0 :: fieldNamesTail := fieldNames.toList | return e
  let (fn0, fieldArgs0) := field0.getAppFnArgs
  unless fn0 == struct ++ fieldName0 do
    trace[simps.debug] "{fn0} != {struct ++ fieldName0}"
    return e
  let (params', reduct :: _) := fieldArgs0.toList.splitAt numParams | unreachable!
  unless params' == params do
    trace[simps.debug] "{params'} != {params}"
    return e
  trace[simps.debug] "Potential structure-eta-reduct:{indentExpr e}\nto{indentExpr reduct}"
  let allArgs := params.toArray.push reduct
  let isEta ← (fieldsTail.zip fieldNamesTail).allM fun (field, fieldName) =>
    if field.getAppFnArgs == (struct ++ fieldName, allArgs) then pure true else isProof field
  unless isEta do return e
  trace[simps.debug] "Structure-eta-reduce:{indentExpr e}\nto{indentExpr reduct}"
  headStructureEtaReduce reduct

中文:
定义 headStructureEtaReduce
  签名: (e : Expr)
  定义体: do
  let env ← getEnv
  let (ctor, args) := e.getAppFnArgs
  let some (.ctorInfo { induct := struct, numParams, ..}) := env.find? ctor | pure e
  let some { fieldNames, .. } := getStructureInfo? env struct | pure e
  let (params, fields) := args.toList.splitAt numParams -- fix if `Array.take` / `Array.drop` exist
  trace[simps.debug]
    "rhs is constructor application with params{indentD params}\nand fields {indentD fields}"
  let field0 :: fieldsTail := fields | return e
  let fieldName0 :: fieldNamesTail := fieldNames.toList | return e
  let (fn0, fieldArgs0) := field0.getAppFnArgs
  unless fn0 == struct ++ fieldName0 do
    trace[simps.debug] "{fn0} != {struct ++ fieldName0}"
    return e
  let (params', reduct :: _) := fieldArgs0.toList.splitAt numParams | unreachable!
  unless params' == params do
    trace[simps.debug] "{params'} != {params}"
    return e
  trace[simps.debug] "Potential structure-eta-reduct:{indentExpr e}\nto{indentExpr reduct}"
  let allArgs := params.toArray.push reduct
  let isEta ← (fieldsTail.zip fieldNamesTail).allM fun (field, fieldName) =>
    if field.getAppFnArgs == (struct ++ fieldName, allArgs) then pure true else isProof field
  unless isEta do return e
  trace[simps.debug] "Structure-eta-reduce:{indentExpr e}\nto{indentExpr reduct}"
  headStructureEtaReduce reduct
-/
partial def headStructureEtaReduce (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let (ctor, args) := e.getAppFnArgs
  let some (.ctorInfo { induct := struct, numParams, ..}) := env.find? ctor | pure e
  let some { fieldNames, .. } := getStructureInfo? env struct | pure e
  let (params, fields) := args.toList.splitAt numParams -- fix if `Array.take` / `Array.drop` exist
  trace[simps.debug]
    "rhs is constructor application with params{indentD params}\nand fields {indentD fields}"
  let field0 :: fieldsTail := fields | return e
  let fieldName0 :: fieldNamesTail := fieldNames.toList | return e
  let (fn0, fieldArgs0) := field0.getAppFnArgs
  unless fn0 == struct ++ fieldName0 do
    trace[simps.debug] "{fn0} != {struct ++ fieldName0}"
    return e
  let (params', reduct :: _) := fieldArgs0.toList.splitAt numParams | unreachable!
  unless params' == params do
    trace[simps.debug] "{params'} != {params}"
    return e
  trace[simps.debug] "Potential structure-eta-reduct:{indentExpr e}\nto{indentExpr reduct}"
  let allArgs := params.toArray.push reduct
  let isEta ← (fieldsTail.zip fieldNamesTail).allM fun (field, fieldName) =>
    if field.getAppFnArgs == (struct ++ fieldName, allArgs) then pure true else isProof field
  unless isEta do return e
  trace[simps.debug] "Structure-eta-reduce:{indentExpr e}\nto{indentExpr reduct}"
  headStructureEtaReduce reduct

/--
Definition of `addProjections` / `addProjections` 的定义

English:
definition addProjections
  signature: (nm : NameStruct) (type lhs rhs : Expr)
  body: do
  -- we don't want to unfold non-reducible definitions (like `Set`) to apply more arguments
  trace[simps.debug] "Type of the Expression before normalizing: {type}"
withTransparency cfg.typeMd forallTelescopeReducing type fun typeArgs tgt => withDefault do
  trace[simps.debug] "Type after removing pi's: {tgt}"
  -- TODO: consider reducing the type less aggressively.
  -- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Simps.20and.20.60def.60/near/560586075
  let tgtWhnf ← whnfD tgt
  trace[simps.debug] "Type after reduction: {tgtWhnf}"
  let newArgs := args ++ typeArgs
  let lhsAp := lhs.instantiateLambdasOrApps typeArgs
  let rhsAp := rhs.instantiateLambdasOrApps typeArgs
  let str := tgtWhnf.getAppFn.constName
  trace[simps.debug] "todo: {todo}, toApply: {toApply}"
  -- We want to generate the current projection if it is in `todo`
  let todoNext := todo.filter (·.1 != "")
  let env ← getEnv
.map (·.2) let stx? := todo.find? (·.1 == "")
  /- The syntax object associated to the projection we're making now (if any).
  Note that we use `ref[0]` so that with `simps (config := ...)` we associate it to the word `simps`
  instead of the application of the attribute to arguments. -/
  let stxProj := stx?.getD ref[0]
  let strInfo? := getStructureInfo? env str
  /- Don't recursively continue if `str` is not a structure or if the structure is in
  `notRecursive`. -/
  if strInfo?.isNone ||
    (todo.isEmpty && str in cfg.notRecursive && !mustBeStr && toApply.isEmpty) then
    if mustBeStr then
      throwError "Invalid `simps` attribute. Target {str} is not a structure"
    if !todoNext.isEmpty && str ∉ cfg.notRecursive then
      let firstTodo := todoNext.head!.1
      throwError "Invalid simp lemma {nm.update firstTodo false |>.toName}.\nProjection \
        {(splitOnNotNumber firstTodo "_")[1]!} doesn't exist, \
        because target {str} is not a structure."
    if cfg.fullyApplied then
      addProjection stxProj univs nm.toName tgt lhsAp rhsAp newArgs cfg
    else
      addProjection stxProj univs nm.toName type lhs rhs args cfg
    return #[nm.toName]
  -- if the type is a structure
  let some (.inductInfo { isRec := false, ctors := [ctor], .. }) := env.find? str | unreachable!
  trace[simps.debug] "{str} is a structure with constructor {ctor}."
  let rhsEta ← headStructureEtaReduce rhsAp
  -- did the user ask to add this projection?
  let addThisProjection := stx?.isSome && toApply.isEmpty
  if addThisProjection then
    -- we pass the precise argument of simps as syntax argument to `addProjection`
    if cfg.fullyApplied then
      addProjection stxProj univs nm.toName tgt lhsAp rhsEta newArgs cfg
    else
      addProjection stxProj univs nm.toName type lhs rhs args cfg
let rhsWhnf ← withTransparency cfg.rhsMd whnf rhsEta
  trace[simps.debug] "The right-hand-side {indentExpr rhsAp}\n reduces to {indentExpr rhsWhnf}"
  if !rhsWhnf.getAppFn.isConstOf ctor then
    -- if I'm about to run into an error, try to set the transparency for `rhsMd` higher.
    if cfg.rhsMd == .reducible && (mustBeStr || !todoNext.isEmpty || !toApply.isEmpty) then
      trace[simps.debug] "Using relaxed reducibility."
      Linter.logLintIf linter.simpsNoConstructor ref m!"\
        The definition {nm.toName} is not a constructor application. \
        Please use `@[simps!]` instead.\n\
        \n\
        Explanation: `@[simps]` uses the definition to find what the simp lemmas should \
        be. If the definition is a constructor, then this is easy, since the values of the \
        projections are just the arguments to the constructor. If the definition is not a \
        constructor, then `@[simps]` will unfold the right-hand side until it has found a \
        constructor application, and uses those values.\n\n\
        This might not always result in the simp-lemmas you want, so you are advised to use \
        `@[simps?]` to double-check whether `@[simps]` generated satisfactory lemmas.\n\
        Note 1: `@[simps!]` also calls the `simp` tactic, and this can be expensive in certain \
        cases.\n\
        Note 2: `@[simps!]` is equivalent to `@[simps (config := \{rhsMd := .default, \
        simpRhs := true})]`. You can also try `@[simps (config := \{rhsMd := .default})]` \
        to still unfold the definitions, but avoid calling `simp` on the resulting statement.\n\
        Note 3: You need `simps!` if not all fields are given explicitly in this definition, \
        even if the definition is a constructor application. For example, if you give a \
        `MulEquiv` by giving the corresponding `Equiv` and the proof that it respects \
        multiplication, then you need to mark it as `@[simps!]`, since the attribute needs to \
        unfold the corresponding `Equiv` to get to the `toFun` field."
      let nms ← addProjections nm type lhs rhs args mustBeStr
        { cfg with rhsMd := .default, simpRhs := true } todo toApply
      return if addThisProjection then nms.push nm.toName else nms
    if !toApply.isEmpty then
      throwError "Invalid simp lemma {nm.toName}.\nThe given definition is not a constructor \
        application:{indentExpr rhsWhnf}"
    if mustBeStr then
      throwError "Invalid `simps` attribute. The body is not a constructor application:\
        {indentExpr rhsWhnf}"
    if !todoNext.isEmpty then
      throwError "Invalid simp lemma {nm.update todoNext.head!.1 false |>.toName}.\n\
        The given definition is not a constructor application:{indentExpr rhsWhnf}"
    if !addThisProjection then
      if cfg.fullyApplied then
        addProjection stxProj univs nm.toName tgt lhsAp rhsEta newArgs cfg
      else
        addProjection stxProj univs nm.toName type lhs rhs args cfg
    return #[nm.toName]
  -- if the value is a constructor application
  trace[simps.debug] "Generating raw projection information..."
  let projInfo ← getProjectionExprs ref tgtWhnf rhsWhnf cfg
  trace[simps.debug] "Raw projection information:{indentD m!"{projInfo}"}"
  -- If we are in the middle of a composite projection.
  if let idx :: rest := toApply then
    let some ⟨newRhs, _⟩ := projInfo[idx]?
      | throwError "unreachable: index of composite projection is out of bounds."
    let newType ← inferType newRhs
    trace[simps.debug] "Applying a custom composite projection. Todo: {toApply}. Current lhs:\
      {indentExpr lhsAp}"
    return ← addProjections nm newType lhsAp newRhs newArgs false cfg todo rest
  trace[simps.debug] "Not in the middle of applying a custom composite projection"
  /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
  automatically choose projections -/
  if todo.length == 1 && todo.head!.1 == "" then return #[nm.toName]
  let projs : Array Name := projInfo.map fun x => x.2.name
  let todo := todoNext
  trace[simps.debug] "Next todo: {todoNext}"
  -- check whether all elements in `todo` have a projection as prefix
  if let some (x, _) := todo.find? fun (x, _) => projs.all
    fun proj => !isPrefixOfAndNotNumber (proj.lastComponentAsString ++ "_") x then
.toName let simpLemma := nm.update x
    let neededProj := (splitOnNotNumber x "_")[0]!
    throwError "Invalid simp lemma {simpLemma}. \
      Structure {str} does not have projection {neededProj}.\n\
      The known projections are:\
      {indentD <| toMessageData projs}\n\
      You can also see this information by running\
      \n `initialize_simps_projections? {str}`.\n\
      Note: these projection names might be customly defined for `simps`, \
      and could differ from the projection names of the structure."
  let nms ← projInfo.flatMapM fun ⟨newRhs, proj, projExpr, projNrs, isDefault, isPrefix⟩ => do
    let newType ← inferType newRhs
    let newTodo := todo.filterMap
      fun (x, stx) => (dropPrefixIfNotNumber? x (proj.lastComponentAsString ++ "_")).map
        (·.toString, stx)
    -- we only continue with this field if it is default or mentioned in todo
    if !(isDefault && todo.isEmpty) && newTodo.isEmpty then return #[]
    let newLhs := projExpr.instantiateLambdasOrApps #[lhsAp]
    let newName := nm.update proj.lastComponentAsString isPrefix
    trace[simps.debug] "Recursively add projections for:{indentExpr newLhs}"
    addProjections newName newType newLhs newRhs newArgs false cfg newTodo projNrs
  return if addThisProjection then nms.push nm.toName else nms

中文:
定义 addProjections
  签名: (nm : NameStruct) (type lhs rhs : Expr)
  定义体: do
  -- we don't want to unfold non-reducible definitions (like `Set`) to apply more arguments
  trace[simps.debug] "Type of the Expression before normalizing: {type}"
withTransparency cfg.typeMd forallTelescopeReducing type fun typeArgs tgt => withDefault do
  trace[simps.debug] "Type after removing pi's: {tgt}"
  -- TODO: consider reducing the type less aggressively.
  -- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Simps.20and.20.60def.60/near/560586075
  let tgtWhnf ← whnfD tgt
  trace[simps.debug] "Type after reduction: {tgtWhnf}"
  let newArgs := args ++ typeArgs
  let lhsAp := lhs.instantiateLambdasOrApps typeArgs
  let rhsAp := rhs.instantiateLambdasOrApps typeArgs
  let str := tgtWhnf.getAppFn.constName
  trace[simps.debug] "todo: {todo}, toApply: {toApply}"
  -- We want to generate the current projection if it is in `todo`
  let todoNext := todo.filter (·.1 != "")
  let env ← getEnv
.map (·.2) let stx? := todo.find? (·.1 == "")
  /- The syntax object associated to the projection we're making now (if any).
  Note that we use `ref[0]` so that with `simps (config := ...)` we associate it to the word `simps`
  instead of the application of the attribute to arguments. -/
  let stxProj := stx?.getD ref[0]
  let strInfo? := getStructureInfo? env str
  /- Don't recursively continue if `str` is not a structure or if the structure is in
  `notRecursive`. -/
  if strInfo?.isNone ||
    (todo.isEmpty && str in cfg.notRecursive && !mustBeStr && toApply.isEmpty) then
    if mustBeStr then
      throwError "Invalid `simps` attribute. Target {str} is not a structure"
    if !todoNext.isEmpty && str ∉ cfg.notRecursive then
      let firstTodo := todoNext.head!.1
      throwError "Invalid simp lemma {nm.update firstTodo false |>.toName}.\nProjection \
        {(splitOnNotNumber firstTodo "_")[1]!} doesn't exist, \
        because target {str} is not a structure."
    if cfg.fullyApplied then
      addProjection stxProj univs nm.toName tgt lhsAp rhsAp newArgs cfg
    else
      addProjection stxProj univs nm.toName type lhs rhs args cfg
    return #[nm.toName]
  -- if the type is a structure
  let some (.inductInfo { isRec := false, ctors := [ctor], .. }) := env.find? str | unreachable!
  trace[simps.debug] "{str} is a structure with constructor {ctor}."
  let rhsEta ← headStructureEtaReduce rhsAp
  -- did the user ask to add this projection?
  let addThisProjection := stx?.isSome && toApply.isEmpty
  if addThisProjection then
    -- we pass the precise argument of simps as syntax argument to `addProjection`
    if cfg.fullyApplied then
      addProjection stxProj univs nm.toName tgt lhsAp rhsEta newArgs cfg
    else
      addProjection stxProj univs nm.toName type lhs rhs args cfg
let rhsWhnf ← withTransparency cfg.rhsMd whnf rhsEta
  trace[simps.debug] "The right-hand-side {indentExpr rhsAp}\n reduces to {indentExpr rhsWhnf}"
  if !rhsWhnf.getAppFn.isConstOf ctor then
    -- if I'm about to run into an error, try to set the transparency for `rhsMd` higher.
    if cfg.rhsMd == .reducible && (mustBeStr || !todoNext.isEmpty || !toApply.isEmpty) then
      trace[simps.debug] "Using relaxed reducibility."
      Linter.logLintIf linter.simpsNoConstructor ref m!"\
        The definition {nm.toName} is not a constructor application. \
        Please use `@[simps!]` instead.\n\
        \n\
        Explanation: `@[simps]` uses the definition to find what the simp lemmas should \
        be. If the definition is a constructor, then this is easy, since the values of the \
        projections are just the arguments to the constructor. If the definition is not a \
        constructor, then `@[simps]` will unfold the right-hand side until it has found a \
        constructor application, and uses those values.\n\n\
        This might not always result in the simp-lemmas you want, so you are advised to use \
        `@[simps?]` to double-check whether `@[simps]` generated satisfactory lemmas.\n\
        Note 1: `@[simps!]` also calls the `simp` tactic, and this can be expensive in certain \
        cases.\n\
        Note 2: `@[simps!]` is equivalent to `@[simps (config := \{rhsMd := .default, \
        simpRhs := true})]`. You can also try `@[simps (config := \{rhsMd := .default})]` \
        to still unfold the definitions, but avoid calling `simp` on the resulting statement.\n\
        Note 3: You need `simps!` if not all fields are given explicitly in this definition, \
        even if the definition is a constructor application. For example, if you give a \
        `MulEquiv` by giving the corresponding `Equiv` and the proof that it respects \
        multiplication, then you need to mark it as `@[simps!]`, since the attribute needs to \
        unfold the corresponding `Equiv` to get to the `toFun` field."
      let nms ← addProjections nm type lhs rhs args mustBeStr
        { cfg with rhsMd := .default, simpRhs := true } todo toApply
      return if addThisProjection then nms.push nm.toName else nms
    if !toApply.isEmpty then
      throwError "Invalid simp lemma {nm.toName}.\nThe given definition is not a constructor \
        application:{indentExpr rhsWhnf}"
    if mustBeStr then
      throwError "Invalid `simps` attribute. The body is not a constructor application:\
        {indentExpr rhsWhnf}"
    if !todoNext.isEmpty then
      throwError "Invalid simp lemma {nm.update todoNext.head!.1 false |>.toName}.\n\
        The given definition is not a constructor application:{indentExpr rhsWhnf}"
    if !addThisProjection then
      if cfg.fullyApplied then
        addProjection stxProj univs nm.toName tgt lhsAp rhsEta newArgs cfg
      else
        addProjection stxProj univs nm.toName type lhs rhs args cfg
    return #[nm.toName]
  -- if the value is a constructor application
  trace[simps.debug] "Generating raw projection information..."
  let projInfo ← getProjectionExprs ref tgtWhnf rhsWhnf cfg
  trace[simps.debug] "Raw projection information:{indentD m!"{projInfo}"}"
  -- If we are in the middle of a composite projection.
  if let idx :: rest := toApply then
    let some ⟨newRhs, _⟩ := projInfo[idx]?
      | throwError "unreachable: index of composite projection is out of bounds."
    let newType ← inferType newRhs
    trace[simps.debug] "Applying a custom composite projection. Todo: {toApply}. Current lhs:\
      {indentExpr lhsAp}"
    return ← addProjections nm newType lhsAp newRhs newArgs false cfg todo rest
  trace[simps.debug] "Not in the middle of applying a custom composite projection"
  /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
  automatically choose projections -/
  if todo.length == 1 && todo.head!.1 == "" then return #[nm.toName]
  let projs : Array Name := projInfo.map fun x => x.2.name
  let todo := todoNext
  trace[simps.debug] "Next todo: {todoNext}"
  -- check whether all elements in `todo` have a projection as prefix
  if let some (x, _) := todo.find? fun (x, _) => projs.all
    fun proj => !isPrefixOfAndNotNumber (proj.lastComponentAsString ++ "_") x then
.toName let simpLemma := nm.update x
    let neededProj := (splitOnNotNumber x "_")[0]!
    throwError "Invalid simp lemma {simpLemma}. \
      Structure {str} does not have projection {neededProj}.\n\
      The known projections are:\
      {indentD <| toMessageData projs}\n\
      You can also see this information by running\
      \n `initialize_simps_projections? {str}`.\n\
      Note: these projection names might be customly defined for `simps`, \
      and could differ from the projection names of the structure."
  let nms ← projInfo.flatMapM fun ⟨newRhs, proj, projExpr, projNrs, isDefault, isPrefix⟩ => do
    let newType ← inferType newRhs
    let newTodo := todo.filterMap
      fun (x, stx) => (dropPrefixIfNotNumber? x (proj.lastComponentAsString ++ "_")).map
        (·.toString, stx)
    -- we only continue with this field if it is default or mentioned in todo
    if !(isDefault && todo.isEmpty) && newTodo.isEmpty then return #[]
    let newLhs := projExpr.instantiateLambdasOrApps #[lhsAp]
    let newName := nm.update proj.lastComponentAsString isPrefix
    trace[simps.debug] "Recursively add projections for:{indentExpr newLhs}"
    addProjections newName newType newLhs newRhs newArgs false cfg newTodo projNrs
  return if addThisProjection then nms.push nm.toName else nms
-/
private partial def addProjections (nm : NameStruct) (type lhs rhs : Expr)
    (args : Array Expr) (mustBeStr : Bool) (cfg : Config)
    (todo : List (String × Syntax)) (toApply : List Nat) : MetaM (Array Name) := do
  -- we don't want to unfold non-reducible definitions (like `Set`) to apply more arguments
  trace[simps.debug] "Type of the Expression before normalizing: {type}"
withTransparency cfg.typeMd forallTelescopeReducing type fun typeArgs tgt => withDefault do
  trace[simps.debug] "Type after removing pi's: {tgt}"
  -- TODO: consider reducing the type less aggressively.
  -- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Simps.20and.20.60def.60/near/560586075
  let tgtWhnf ← whnfD tgt
  trace[simps.debug] "Type after reduction: {tgtWhnf}"
  let newArgs := args ++ typeArgs
  let lhsAp := lhs.instantiateLambdasOrApps typeArgs
  let rhsAp := rhs.instantiateLambdasOrApps typeArgs
  let str := tgtWhnf.getAppFn.constName
  trace[simps.debug] "todo: {todo}, toApply: {toApply}"
  -- We want to generate the current projection if it is in `todo`
  let todoNext := todo.filter (·.1 != "")
  let env ← getEnv
.map (·.2) let stx? := todo.find? (·.1 == "")
  /- The syntax object associated to the projection we're making now (if any).
  Note that we use `ref[0]` so that with `simps (config := ...)` we associate it to the word `simps`
  instead of the application of the attribute to arguments. -/
  let stxProj := stx?.getD ref[0]
  let strInfo? := getStructureInfo? env str
  /- Don't recursively continue if `str` is not a structure or if the structure is in
  `notRecursive`. -/
  if strInfo?.isNone ||
    (todo.isEmpty && str in cfg.notRecursive && !mustBeStr && toApply.isEmpty) then
    if mustBeStr then
      throwError "Invalid `simps` attribute. Target {str} is not a structure"
    if !todoNext.isEmpty && str ∉ cfg.notRecursive then
      let firstTodo := todoNext.head!.1
      throwError "Invalid simp lemma {nm.update firstTodo false |>.toName}.\nProjection \
        {(splitOnNotNumber firstTodo "_")[1]!} doesn't exist, \
        because target {str} is not a structure."
    if cfg.fullyApplied then
      addProjection stxProj univs nm.toName tgt lhsAp rhsAp newArgs cfg
    else
      addProjection stxProj univs nm.toName type lhs rhs args cfg
    return #[nm.toName]
  -- if the type is a structure
  let some (.inductInfo { isRec := false, ctors := [ctor], .. }) := env.find? str | unreachable!
  trace[simps.debug] "{str} is a structure with constructor {ctor}."
  let rhsEta ← headStructureEtaReduce rhsAp
  -- did the user ask to add this projection?
  let addThisProjection := stx?.isSome && toApply.isEmpty
  if addThisProjection then
    -- we pass the precise argument of simps as syntax argument to `addProjection`
    if cfg.fullyApplied then
      addProjection stxProj univs nm.toName tgt lhsAp rhsEta newArgs cfg
    else
      addProjection stxProj univs nm.toName type lhs rhs args cfg
let rhsWhnf ← withTransparency cfg.rhsMd whnf rhsEta
  trace[simps.debug] "The right-hand-side {indentExpr rhsAp}\n reduces to {indentExpr rhsWhnf}"
  if !rhsWhnf.getAppFn.isConstOf ctor then
    -- if I'm about to run into an error, try to set the transparency for `rhsMd` higher.
    if cfg.rhsMd == .reducible && (mustBeStr || !todoNext.isEmpty || !toApply.isEmpty) then
      trace[simps.debug] "Using relaxed reducibility."
      Linter.logLintIf linter.simpsNoConstructor ref m!"\
        The definition {nm.toName} is not a constructor application. \
        Please use `@[simps!]` instead.\n\
        \n\
        Explanation: `@[simps]` uses the definition to find what the simp lemmas should \
        be. If the definition is a constructor, then this is easy, since the values of the \
        projections are just the arguments to the constructor. If the definition is not a \
        constructor, then `@[simps]` will unfold the right-hand side until it has found a \
        constructor application, and uses those values.\n\n\
        This might not always result in the simp-lemmas you want, so you are advised to use \
        `@[simps?]` to double-check whether `@[simps]` generated satisfactory lemmas.\n\
        Note 1: `@[simps!]` also calls the `simp` tactic, and this can be expensive in certain \
        cases.\n\
        Note 2: `@[simps!]` is equivalent to `@[simps (config := \{rhsMd := .default, \
        simpRhs := true})]`. You can also try `@[simps (config := \{rhsMd := .default})]` \
        to still unfold the definitions, but avoid calling `simp` on the resulting statement.\n\
        Note 3: You need `simps!` if not all fields are given explicitly in this definition, \
        even if the definition is a constructor application. For example, if you give a \
        `MulEquiv` by giving the corresponding `Equiv` and the proof that it respects \
        multiplication, then you need to mark it as `@[simps!]`, since the attribute needs to \
        unfold the corresponding `Equiv` to get to the `toFun` field."
      let nms ← addProjections nm type lhs rhs args mustBeStr
        { cfg with rhsMd := .default, simpRhs := true } todo toApply
      return if addThisProjection then nms.push nm.toName else nms
    if !toApply.isEmpty then
      throwError "Invalid simp lemma {nm.toName}.\nThe given definition is not a constructor \
        application:{indentExpr rhsWhnf}"
    if mustBeStr then
      throwError "Invalid `simps` attribute. The body is not a constructor application:\
        {indentExpr rhsWhnf}"
    if !todoNext.isEmpty then
      throwError "Invalid simp lemma {nm.update todoNext.head!.1 false |>.toName}.\n\
        The given definition is not a constructor application:{indentExpr rhsWhnf}"
    if !addThisProjection then
      if cfg.fullyApplied then
        addProjection stxProj univs nm.toName tgt lhsAp rhsEta newArgs cfg
      else
        addProjection stxProj univs nm.toName type lhs rhs args cfg
    return #[nm.toName]
  -- if the value is a constructor application
  trace[simps.debug] "Generating raw projection information..."
  let projInfo ← getProjectionExprs ref tgtWhnf rhsWhnf cfg
  trace[simps.debug] "Raw projection information:{indentD m!"{projInfo}"}"
  -- If we are in the middle of a composite projection.
  if let idx :: rest := toApply then
    let some ⟨newRhs, _⟩ := projInfo[idx]?
      | throwError "unreachable: index of composite projection is out of bounds."
    let newType ← inferType newRhs
    trace[simps.debug] "Applying a custom composite projection. Todo: {toApply}. Current lhs:\
      {indentExpr lhsAp}"
    return ← addProjections nm newType lhsAp newRhs newArgs false cfg todo rest
  trace[simps.debug] "Not in the middle of applying a custom composite projection"
  /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
  automatically choose projections -/
  if todo.length == 1 && todo.head!.1 == "" then return #[nm.toName]
  let projs : Array Name := projInfo.map fun x => x.2.name
  let todo := todoNext
  trace[simps.debug] "Next todo: {todoNext}"
  -- check whether all elements in `todo` have a projection as prefix
  if let some (x, _) := todo.find? fun (x, _) => projs.all
    fun proj => !isPrefixOfAndNotNumber (proj.lastComponentAsString ++ "_") x then
.toName let simpLemma := nm.update x
    let neededProj := (splitOnNotNumber x "_")[0]!
    throwError "Invalid simp lemma {simpLemma}. \
      Structure {str} does not have projection {neededProj}.\n\
      The known projections are:\
      {indentD <| toMessageData projs}\n\
      You can also see this information by running\
      \n `initialize_simps_projections? {str}`.\n\
      Note: these projection names might be customly defined for `simps`, \
      and could differ from the projection names of the structure."
  let nms ← projInfo.flatMapM fun ⟨newRhs, proj, projExpr, projNrs, isDefault, isPrefix⟩ => do
    let newType ← inferType newRhs
    let newTodo := todo.filterMap
      fun (x, stx) => (dropPrefixIfNotNumber? x (proj.lastComponentAsString ++ "_")).map
        (·.toString, stx)
    -- we only continue with this field if it is default or mentioned in todo
    if !(isDefault && todo.isEmpty) && newTodo.isEmpty then return #[]
    let newLhs := projExpr.instantiateLambdasOrApps #[lhsAp]
    let newName := nm.update proj.lastComponentAsString isPrefix
    trace[simps.debug] "Recursively add projections for:{indentExpr newLhs}"
    addProjections newName newType newLhs newRhs newArgs false cfg newTodo projNrs
  return if addThisProjection then nms.push nm.toName else nms

end Simps
open Simps

/--
Definition of `simpsTac` / `simpsTac` 的定义

English:
definition simpsTac
  signature: (ref : Syntax) (nm : Name) (cfg : Config := {})
  body: withOptions (fun o => if trc then o.set `trace.simps.verbose true else o) do
  -- We need access to theorem bodies
  let env ← withoutExporting getEnv
  let some d := env.find? nm | throwError "Declaration {nm} doesn't exist."
let lhs : Expr := mkConst d.name d.levelParams.map Level.param
.map fun (proj, stx) => (proj ++ "_", stx) let todo := todo.eraseDups
  let mut cfg := cfg
  let nm : NameStruct :=
    { parent := nm.getPrefix
      components :=
        if let some n := cfg.nameStem then
          if n == "" then [] else [n]
        else
          let s := nm.lastComponentAsString
          if (← isInstance nm) ∧ s.startsWith "inst" then [] else [s]}
MetaM.run' addProjections ref d.levelParams
    nm d.type lhs (d.value! (allowOpaque := true)) #[] (mustBeStr := true) cfg todo []

中文:
定义 simpsTac
  签名: (ref : Syntax) (nm : Name) (cfg : 余nfig := {})
  定义体: withOptions (fun o => if trc then o.set `trace.simps.verbose true else o) do
  -- We need access to theorem bodies
  let env ← withoutExporting getEnv
  let some d := env.find? nm | throwError "Declaration {nm} doesn't exist."
let lhs : Expr := mkConst d.name d.levelParams.map Level.param
.map fun (proj, stx) => (proj ++ "_", stx) let todo := todo.eraseDups
  let mut cfg := cfg
  let nm : NameStruct :=
    { parent := nm.getPrefix
      components :=
        if let some n := cfg.nameStem then
          if n == "" then [] else [n]
        else
          let s := nm.lastComponentAsString
          if (← isInstance nm) ∧ s.startsWith "inst" then [] else [s]}
MetaM.run' addProjections ref d.levelParams
    nm d.type lhs (d.value! (allowOpaque := true)) #[] (mustBeStr := true) cfg todo []
-/
def simpsTac (ref : Syntax) (nm : Name) (cfg : Config := {})
    (todo : List (String × Syntax) := []) (trc := false) : AttrM (Array Name) :=
  withOptions (fun o => if trc then o.set `trace.simps.verbose true else o) do
  -- We need access to theorem bodies
  let env ← withoutExporting getEnv
  let some d := env.find? nm | throwError "Declaration {nm} doesn't exist."
let lhs : Expr := mkConst d.name d.levelParams.map Level.param
.map fun (proj, stx) => (proj ++ "_", stx) let todo := todo.eraseDups
  let mut cfg := cfg
  let nm : NameStruct :=
    { parent := nm.getPrefix
      components :=
        if let some n := cfg.nameStem then
          if n == "" then [] else [n]
        else
          let s := nm.lastComponentAsString
          if (← isInstance nm) ∧ s.startsWith "inst" then [] else [s]}
MetaM.run' addProjections ref d.levelParams
    nm d.type lhs (d.value! (allowOpaque := true)) #[] (mustBeStr := true) cfg todo []

/--
Definition of `simpsTacFromSyntax` / `simpsTacFromSyntax` 的定义

English:
definition simpsTacFromSyntax
  signature: (nm : Name) (stx : Syntax)
  body: match stx with
  | `(attr| simps $[!%$bang]? $[?%$trc]? $c:simpsConfig $[$ids]*) => do
    let cfg ← elabSimpsConfig c
    let cfg := if bang.isNone then cfg else { cfg with rhsMd := .default, simpRhs := true }
    let ids := ids.map fun x => (x.getId.eraseMacroScopes.lastComponentAsString, x.raw)
    simpsTac stx nm cfg ids.toList trc.isSome
  | _ => throwUnsupportedSyntax

中文:
定义 simpsTacFromSyntax
  签名: (nm : Name) (stx : Syntax)
  定义体: match stx with
  | `(attr| simps $[!%$bang]? $[?%$trc]? $c:simpsConfig $[$ids]*) => do
    let cfg ← elabSimpsConfig c
    let cfg := if bang.isNone then cfg else { cfg with rhsMd := .default, simpRhs := true }
    let ids := ids.map fun x => (x.getId.eraseMacroScopes.lastComponentAsString, x.raw)
    simpsTac stx nm cfg ids.toList trc.isSome
  | _ => throwUnsupportedSyntax

Depends on / 依赖: bang.isNone, elabSimpsConfig, eraseMacroScopes, ids.map, ids.toList, isNone, isSome, lastComponentAsString, simpRhs, simpsConfig, simpsTac, throwUnsupportedSyntax, toList, trc.isSome, x.getId.eraseMacroScopes.lastComponentAsString, x.raw
-/
def simpsTacFromSyntax (nm : Name) (stx : Syntax) : AttrM (Array Name) :=
  match stx with
  | `(attr| simps $[!%$bang]? $[?%$trc]? $c:simpsConfig $[$ids]*) => do
    let cfg ← elabSimpsConfig c
    let cfg := if bang.isNone then cfg else { cfg with rhsMd := .default, simpRhs := true }
    let ids := ids.map fun x => (x.getId.eraseMacroScopes.lastComponentAsString, x.raw)
    simpsTac stx nm cfg ids.toList trc.isSome
  | _ => throwUnsupportedSyntax

/-- The `simps` attribute. -/
initialize simpsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `simps
    /- So as to be run _after_ the `instance` attribute, as this handler uses
    `Lean.Meta.isInstance`, which requires the `instance` handler to have
    already run. -/
    applicationTime := .afterCompilation
    descr := "Automatically derive lemmas specifying the projections of this declaration.",
    getParam := simpsTacFromSyntax }

initialize Mathlib.Tactic.registerGeneratingAttr `simps fun decl stx kind => do
  simpsAttr.attr.add decl stx kind
  return (simpsAttr.getParam? (← getEnv) decl).get!
