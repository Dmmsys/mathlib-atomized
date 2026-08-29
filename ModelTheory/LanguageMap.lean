/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.ModelTheory.Basic

/-!
# Language Maps

Maps between first-order languages in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions

- A `FirstOrder.Language.LHom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
- A `FirstOrder.Language.LEquiv`, denoted `L ≃ᴸ L'`, is an invertible language homomorphism.
- `FirstOrder.Language.withConstants` is defined so that if `M` is an `L.Structure` and
  `A : Set M`, `L.withConstants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum
  hypothesis*][flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]

-/

@[expose] public section

universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

/--
Definition of `LHom` / `LHom` 的定义

English:
structure LHom
  parameters: where
  axioms and operations (2):
    - onFunction : forall ⦃n⦄, L.Functions n -> L'.Functions n  [default: by exact fun {n} => isEmptyElim]
    - onRelation : forall ⦃n⦄, L.Relations n -> L'.Relations n  [default: by exact fun {n} => isEmptyElim]

中文:
结构 L态射
  参数: where
  公理与运算 (2 个):
    - onFunction : 对任意 ⦃n⦄, L.函数 n -> L'.函数 n  [默认: by exact fun {n} => isEmptyElim]
    - onRelation : 对任意 ⦃n⦄, L.关系 n -> L'.关系 n  [默认: by exact fun {n} => isEmptyElim]

Depends on / 依赖: isEmptyElim
-/
structure LHom where
  /-- The mapping of functions -/
  onFunction : forall ⦃n⦄, L.Functions n -> L'.Functions n := by
    exact fun {n} => isEmptyElim
  /-- The mapping of relations -/
  onRelation : forall ⦃n⦄, L.Relations n -> L'.Relations n := by
    exact fun {n} => isEmptyElim

@[inherit_doc FirstOrder.Language.LHom]
infixl:10 " ->ᴸ " => LHom

-- \^L
variable {L L'}

namespace LHom

variable (ϕ : L ->ᴸ L')

/-- Pulls a structure back along a language map. -/
@[instance_reducible]
/--
Definition of `reduct` / `reduct` 的定义

English:
definition reduct
  signature: (M : Type*) [L'.Structure M]
  body: funMap (ϕ.onFunction f) xs
  RelMap r xs := RelMap (ϕ.onRelation r) xs

中文:
定义 reduct
  签名: (M : 类型) [L'.结构 M]
  定义体: funMap (ϕ.onFunction f) xs
  RelMap r xs := RelMap (ϕ.onRelation r) xs

Depends on / 依赖: funMap, onFunction
-/
def reduct (M : Type*) [L'.Structure M] : L.Structure M where
  funMap f xs := funMap (ϕ.onFunction f) xs
  RelMap r xs := RelMap (ϕ.onRelation r) xs

/-- The identity language homomorphism. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (L : Language)
  body: ⟨fun _n => id, fun _n => id⟩

中文:
定义 id
  签名: (L : Language)
  定义体: ⟨fun _n => id, fun _n => id⟩
-/
protected def id (L : Language) : L ->ᴸ L :=
  ⟨fun _n => id, fun _n => id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (L ->ᴸ L)
  body: ⟨LHom.id L⟩

中文:
实例 :
  签名: 可居 (L ->ᴸ L)
  定义体: ⟨LHom.id L⟩

Depends on / 依赖: LHom.id
-/
instance : Inhabited (L ->ᴸ L) :=
  ⟨LHom.id L⟩

/-- The inclusion of the left factor into the sum of two languages. -/
@[simps]
/--
Definition of `sumInl` / `sumInl` 的定义

English:
definition sumInl
  signature: : L ->ᴸ L.sum L'
  body: ⟨fun _n => Sum.inl, fun _n => Sum.inl⟩

中文:
定义 sumInl
  签名: : L ->ᴸ L.求和 L'
  定义体: ⟨fun _n => Sum.inl, fun _n => Sum.inl⟩
-/
protected def sumInl : L ->ᴸ L.sum L' :=
  ⟨fun _n => Sum.inl, fun _n => Sum.inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
@[simps]
/--
Definition of `sumInr` / `sumInr` 的定义

English:
definition sumInr
  signature: : L' ->ᴸ L.sum L'
  body: ⟨fun _n => Sum.inr, fun _n => Sum.inr⟩

中文:
定义 sumInr
  签名: : L' ->ᴸ L.求和 L'
  定义体: ⟨fun _n => Sum.inr, fun _n => Sum.inr⟩
-/
protected def sumInr : L' ->ᴸ L.sum L' :=
  ⟨fun _n => Sum.inr, fun _n => Sum.inr⟩

variable (L L')

/-- The inclusion of an empty language into any other language. -/
@[simps]
/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: [L.IsAlgebraic] [L.IsRelational]

中文:
定义 ofIsEmpty
  签名: [L.是代数] [L.IsRelational]
-/
protected def ofIsEmpty [L.IsAlgebraic] [L.IsRelational] : L ->ᴸ L' where

variable {L L'} {L'' : Language}

@[ext]
/--
theorem `funext` / 定理 `funext`

English:
theorem funext
  statement: {F G : L ->ᴸ L'} (h_fun : F.onFunction = G.onFunction)
  proof: by
  obtain ⟨Ff, Fr⟩ := F
  obtain ⟨Gf, Gr⟩ := G
  simp only [mk.injEq]
  exact And.intro h_fun h_rel

中文:
定理 funext
  结论: {F G : L ->ᴸ L'} (h_fun : F.onFunction = G.onFunction)
  证明: by
  obtain ⟨Ff, Fr⟩ := F
  obtain ⟨Gf, Gr⟩ := G
  simp only [mk.injEq]
  exact And.intro h_fun h_rel
-/
protected theorem funext {F G : L ->ᴸ L'} (h_fun : F.onFunction = G.onFunction)
    (h_rel : F.onRelation = G.onRelation) : F = G := by
  obtain ⟨Ff, Fr⟩ := F
  obtain ⟨Gf, Gr⟩ := G
  simp only [mk.injEq]
  exact And.intro h_fun h_rel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.IsAlgebraic]
  signature: [L.IsRelational]
  body: ⟨⟨LHom.ofIsEmpty L L'⟩, fun _ => LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

中文:
实例 [L.是代数]
  签名: [L.IsRelational]
  定义体: ⟨⟨LHom.ofIsEmpty L L'⟩, fun _ => LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

Depends on / 依赖: LHom.funext, LHom.ofIsEmpty, Subsingleton, Subsingleton.elim, ofIsEmpty
-/
instance [L.IsAlgebraic] [L.IsRelational] : Unique (L ->ᴸ L') :=
  ⟨⟨LHom.ofIsEmpty L L'⟩, fun _ => LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- The composition of two language homomorphisms. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : L' ->ᴸ L'') (f : L ->ᴸ L')
  body: ⟨fun _n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩

中文:
定义 comp
  签名: (g : L' ->ᴸ L'') (f : L ->ᴸ L')
  定义体: ⟨fun _n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩
-/
def comp (g : L' ->ᴸ L'') (f : L ->ᴸ L') : L ->ᴸ L'' :=
  ⟨fun _n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩

-- added ᴸ to avoid clash with function composition
@[inherit_doc]
local infixl:60 " ∘ᴸ " => LHom.comp

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (F : L ->ᴸ L')
  statement: LHom.id L' ∘ᴸ F = F
  proof: by
  cases F
  rfl

@[simp]

中文:
定理 id_comp
  条件: (F : L ->ᴸ L')
  结论: L态射.id L' ∘ᴸ F = F
  证明: by
  cases F
  rfl

@[simp]
-/
theorem id_comp (F : L ->ᴸ L') : LHom.id L' ∘ᴸ F = F := by
  cases F
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (F : L ->ᴸ L')
  statement: F ∘ᴸ LHom.id L = F
  proof: by
  cases F
  rfl

中文:
定理 comp_id
  条件: (F : L ->ᴸ L')
  结论: F ∘ᴸ L态射.id L = F
  证明: by
  cases F
  rfl
-/
theorem comp_id (F : L ->ᴸ L') : F ∘ᴸ LHom.id L = F := by
  cases F
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: {L3 : Language} (F : L'' ->ᴸ L3) (G : L' ->ᴸ L'') (H : L ->ᴸ L')
  proof: rfl

中文:
定理 comp_assoc
  条件: {L3 : Language} (F : L'' ->ᴸ L3) (G : L' ->ᴸ L'') (H : L ->ᴸ L')
  证明: rfl
-/
theorem comp_assoc {L3 : Language} (F : L'' ->ᴸ L3) (G : L' ->ᴸ L'') (H : L ->ᴸ L') :
    F ∘ᴸ G ∘ᴸ H = F ∘ᴸ (G ∘ᴸ H) :=
  rfl

section SumElim

variable (ψ : L'' ->ᴸ L')

/-- A language map defined on two factors of a sum. -/
@[simps]
/--
Definition of `sumElim` / `sumElim` 的定义

English:
definition sumElim
  signature: : L.sum L'' ->ᴸ L' where
  body: Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

中文:
定义 sumElim
  签名: : L.求和 L'' ->ᴸ L' where
  定义体: Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f
-/
protected def sumElim : L.sum L'' ->ᴸ L' where
  onFunction _n := Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

/--
theorem `sumElim_comp_inl` / 定理 `sumElim_comp_inl`

English:
theorem sumElim_comp_inl
  given: (ψ : L'' ->ᴸ L')
  statement: ϕ.sumElim ψ ∘ᴸ LHom.sumInl = ϕ
  proof: LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

中文:
定理 sumElim_comp_inl
  条件: (ψ : L'' ->ᴸ L')
  结论: ϕ.sumElim ψ ∘ᴸ L态射.sumInl = ϕ
  证明: LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

Depends on / 依赖: LHom.funext
-/
theorem sumElim_comp_inl (ψ : L'' ->ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInl = ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

/--
theorem `sumElim_comp_inr` / 定理 `sumElim_comp_inr`

English:
theorem sumElim_comp_inr
  given: (ψ : L'' ->ᴸ L')
  statement: ϕ.sumElim ψ ∘ᴸ LHom.sumInr = ψ
  proof: LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

中文:
定理 sumElim_comp_inr
  条件: (ψ : L'' ->ᴸ L')
  结论: ϕ.sumElim ψ ∘ᴸ L态射.sumInr = ψ
  证明: LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

Depends on / 依赖: LHom.funext
-/
theorem sumElim_comp_inr (ψ : L'' ->ᴸ L') : ϕ.sumElim ψ ∘ᴸ LHom.sumInr = ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

/--
theorem `sumElim_inl_inr` / 定理 `sumElim_inl_inr`

English:
theorem sumElim_inl_inr
  statement: LHom.sumInl.sumElim LHom.sumInr = LHom.id (L.sum L')
  proof: LHom.funext (funext fun _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)

中文:
定理 sumElim_inl_inr
  结论: L态射.sumInl.sumElim L态射.sumInr = L态射.id (L.求和 L')
  证明: LHom.funext (funext fun _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)

Depends on / 依赖: LHom.funext, Sum.elim_inl_inr, elim_inl_inr
-/
theorem sumElim_inl_inr : LHom.sumInl.sumElim LHom.sumInr = LHom.id (L.sum L') :=
  LHom.funext (funext fun _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)

/--
theorem `comp_sumElim` / 定理 `comp_sumElim`

English:
theorem comp_sumElim
  given: {L3 : Language} (θ : L' ->ᴸ L3)
  proof: LHom.funext (funext fun _n => Sum.comp_elim _ _ _) (funext fun _n => Sum.comp_elim _ _ _)

中文:
定理 comp_sumElim
  条件: {L3 : Language} (θ : L' ->ᴸ L3)
  证明: LHom.funext (funext fun _n => Sum.comp_elim _ _ _) (funext fun _n => Sum.comp_elim _ _ _)

Depends on / 依赖: LHom.funext, Sum.comp_elim, comp_elim
-/
theorem comp_sumElim {L3 : Language} (θ : L' ->ᴸ L3) :
    θ ∘ᴸ ϕ.sumElim ψ = (θ ∘ᴸ ϕ).sumElim (θ ∘ᴸ ψ) :=
  LHom.funext (funext fun _n => Sum.comp_elim _ _ _) (funext fun _n => Sum.comp_elim _ _ _)

end SumElim

section SumMap

variable {L₁ L₂ : Language} (ψ : L₁ ->ᴸ L₂)

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps]
/--
Definition of `sumMap` / `sumMap` 的定义

English:
definition sumMap
  signature: : L.sum L₁ ->ᴸ L'.sum L₂ where
  body: Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

@[simp]

中文:
定义 sumMap
  签名: : L.求和 L₁ ->ᴸ L'.求和 L₂ where
  定义体: Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

@[simp]

Depends on / 依赖: Sum.map, onFunction
-/
def sumMap : L.sum L₁ ->ᴸ L'.sum L₂ where
  onFunction _n := Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation _n := Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

@[simp]
/--
theorem `sumMap_comp_inl` / 定理 `sumMap_comp_inl`

English:
theorem sumMap_comp_inl
  statement: ϕ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ ϕ
  proof: LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

@[simp]

中文:
定理 sumMap_comp_inl
  结论: ϕ.sumMap ψ ∘ᴸ L态射.sumInl = L态射.sumInl ∘ᴸ ϕ
  证明: LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

@[simp]

Depends on / 依赖: LHom.funext
-/
theorem sumMap_comp_inl : ϕ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

@[simp]
/--
theorem `sumMap_comp_inr` / 定理 `sumMap_comp_inr`

English:
theorem sumMap_comp_inr
  statement: ϕ.sumMap ψ ∘ᴸ LHom.sumInr = LHom.sumInr ∘ᴸ ψ
  proof: LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

中文:
定理 sumMap_comp_inr
  结论: ϕ.sumMap ψ ∘ᴸ L态射.sumInr = L态射.sumInr ∘ᴸ ψ
  证明: LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

Depends on / 依赖: LHom.funext
-/
theorem sumMap_comp_inr : ϕ.sumMap ψ ∘ᴸ LHom.sumInr = LHom.sumInr ∘ᴸ ψ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

end SumMap

/--
Definition of `Injective` / `Injective` 的定义

English:
structure Injective
  parameters: : Prop where
  axioms and operations (2):
    - onFunction({n}) : Function.Injective fun f : L.Functions n => onFunction ϕ f
    - onRelation({n}) : Function.Injective fun R : L.Relations n => onRelation ϕ R

中文:
结构 单射
  参数: : 命题 where
  公理与运算 (2 个):
    - onFunction({n}) : 函数.单射 fun f : L.函数 n => onFunction ϕ f
    - onRelation({n}) : 函数.单射 fun R : L.关系 n => onRelation ϕ R
-/
protected structure Injective : Prop where
  onFunction {n} : Function.Injective fun f : L.Functions n => onFunction ϕ f
  onRelation {n} : Function.Injective fun R : L.Relations n => onRelation ϕ R

/-- Pulls an `L`-structure along a language map `ϕ : L →ᴸ L'`, and then expands it
  to an `L'`-structure arbitrarily. -/
@[instance_reducible]
/--
Definition of `defaultExpansion` / `defaultExpansion` 的定义

English:
definition defaultExpansion
  signature: (ϕ : L ->ᴸ L')
  body: if h' : f in Set.range fun f : L.Functions n => onFunction ϕ f then funMap h'.choose xs
    else default
  RelMap {n} r xs :=
    if h' : r in Set.range fun r : L.Relations n => onRelation ϕ r then RelMap h'.choose xs
    else default

中文:
定义 defaultExpansion
  签名: (ϕ : L ->ᴸ L')
  定义体: if h' : f in Set.range fun f : L.Functions n => onFunction ϕ f then funMap h'.choose xs
    else default
  RelMap {n} r xs :=
    if h' : r in Set.range fun r : L.Relations n => onRelation ϕ r then RelMap h'.choose xs
    else default

Depends on / 依赖: Functions, L.Functions, L.Relations, RelMap, Relations, Set.range, funMap, onFunction, onRelation
-/
noncomputable def defaultExpansion (ϕ : L ->ᴸ L')
    [forall (n) (f : L'.Functions n), Decidable (f in Set.range fun f : L.Functions n => onFunction ϕ f)]
    [forall (n) (r : L'.Relations n), Decidable (r in Set.range fun r : L.Relations n => onRelation ϕ r)]
    (M : Type*) [Inhabited M] [L.Structure M] : L'.Structure M where
  funMap {n} f xs :=
    if h' : f in Set.range fun f : L.Functions n => onFunction ϕ f then funMap h'.choose xs
    else default
  RelMap {n} r xs :=
    if h' : r in Set.range fun r : L.Relations n => onRelation ϕ r then RelMap h'.choose xs
    else default

/--
Definition of `IsExpansionOn` / `IsExpansionOn` 的定义

English:
class IsExpansionOn
  parameters: (M : Type*) [L.Structure M] [L'.Structure M]
  axioms and operations (2):
    - map_onFunction : forall {n} (f : L.Functions n) (x : Fin n -> M), funMap (ϕ.onFunction f) x = funMap f x  [default: by exact fun {n} => isEmptyElim]
    - map_onRelation : forall {n} (R : L.Relations n) (x : Fin n -> M), RelMap (ϕ.onRelation R) x = RelMap R x  [default: by exact fun {n} => isEmptyElim]

中文:
类 是ExpansionOn
  参数: (M : 类型) [L.结构 M] [L'.结构 M]
  公理与运算 (2 个):
    - map_onFunction : 对任意 {n} (f : L.函数 n) (x : 有限集 n -> M), funMap (ϕ.onFunction f) x = funMap f x  [默认: by exact fun {n} => isEmptyElim]
    - map_onRelation : 对任意 {n} (R : L.关系 n) (x : 有限集 n -> M), RelMap (ϕ.onRelation R) x = RelMap R x  [默认: by exact fun {n} => isEmptyElim]

Depends on / 依赖: L.Relations, RelMap, Relations, isEmptyElim, map_onRelation, onRelation
-/
class IsExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] : Prop where
  map_onFunction :
    forall {n} (f : L.Functions n) (x : Fin n -> M), funMap (ϕ.onFunction f) x = funMap f x := by
      exact fun {n} => isEmptyElim
  map_onRelation :
    forall {n} (R : L.Relations n) (x : Fin n -> M), RelMap (ϕ.onRelation R) x = RelMap R x := by
      exact fun {n} => isEmptyElim

@[simp]
/--
theorem `map_onFunction` / 定理 `map_onFunction`

English:
theorem map_onFunction
  statement: {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
  proof: IsExpansionOn.map_onFunction f x

@[simp]

中文:
定理 map_onFunction
  结论: {M : 类型} [L.结构 M] [L'.结构 M] [ϕ.是ExpansionOn M] {n}
  证明: IsExpansionOn.map_onFunction f x

@[simp]

Depends on / 依赖: IsExpansionOn, IsExpansionOn.map_onFunction, map_onFunction
-/
theorem map_onFunction {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (f : L.Functions n) (x : Fin n -> M) : funMap (ϕ.onFunction f) x = funMap f x :=
  IsExpansionOn.map_onFunction f x

@[simp]
/--
theorem `map_onRelation` / 定理 `map_onRelation`

English:
theorem map_onRelation
  statement: {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
  proof: IsExpansionOn.map_onRelation R x

中文:
定理 map_onRelation
  结论: {M : 类型} [L.结构 M] [L'.结构 M] [ϕ.是ExpansionOn M] {n}
  证明: IsExpansionOn.map_onRelation R x

Depends on / 依赖: IsExpansionOn, IsExpansionOn.map_onRelation, map_onRelation
-/
theorem map_onRelation {M : Type*} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n}
    (R : L.Relations n) (x : Fin n -> M) : RelMap (ϕ.onRelation R) x = RelMap R x :=
  IsExpansionOn.map_onRelation R x

/--
Instance `id_isExpansionOn` / 实例 `id_isExpansionOn`

English:
instance id_isExpansionOn
  signature: (M : Type*) [L.Structure M]
  body: ⟨fun _ _ => rfl, fun _ _ => rfl⟩

中文:
实例 id_isExpansionOn
  签名: (M : 类型) [L.结构 M]
  定义体: ⟨fun _ _ => rfl, fun _ _ => rfl⟩
-/
instance id_isExpansionOn (M : Type*) [L.Structure M] : IsExpansionOn (LHom.id L) M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/--
Instance `ofIsEmpty_isExpansionOn` / 实例 `ofIsEmpty_isExpansionOn`

English:
instance ofIsEmpty_isExpansionOn
  signature: (M : Type*) [L.Structure M] [L'.Structure M] [L.IsAlgebraic]

中文:
实例 ofIsEmpty_isExpansionOn
  签名: (M : 类型) [L.结构 M] [L'.结构 M] [L.是代数]
-/
instance ofIsEmpty_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] [L.IsAlgebraic]
    [L.IsRelational] : IsExpansionOn (LHom.ofIsEmpty L L') M where

/--
Instance `sumElim_isExpansionOn` / 实例 `sumElim_isExpansionOn`

English:
instance sumElim_isExpansionOn
  signature: {L'' : Language} (ψ : L'' ->ᴸ L') (M : Type*) [L.Structure M]
  body: ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

中文:
实例 sumElim_isExpansionOn
  签名: {L'' : Language} (ψ : L'' ->ᴸ L') (M : 类型) [L.结构 M]
  定义体: ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

Depends on / 依赖: Sum.casesOn, casesOn
-/
instance sumElim_isExpansionOn {L'' : Language} (ψ : L'' ->ᴸ L') (M : Type*) [L.Structure M]
    [L'.Structure M] [L''.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumElim ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

/--
Instance `sumMap_isExpansionOn` / 实例 `sumMap_isExpansionOn`

English:
instance sumMap_isExpansionOn
  signature: {L₁ L₂ : Language} (ψ : L₁ ->ᴸ L₂) (M : Type*) [L.Structure M]
  body: ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

中文:
实例 sumMap_isExpansionOn
  签名: {L₁ L₂ : Language} (ψ : L₁ ->ᴸ L₂) (M : 类型) [L.结构 M]
  定义体: ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

Depends on / 依赖: Sum.casesOn, casesOn
-/
instance sumMap_isExpansionOn {L₁ L₂ : Language} (ψ : L₁ ->ᴸ L₂) (M : Type*) [L.Structure M]
    [L'.Structure M] [L₁.Structure M] [L₂.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] :
    (ϕ.sumMap ψ).IsExpansionOn M :=
  ⟨fun f _ => Sum.casesOn f (by simp) (by simp), fun R _ => Sum.casesOn R (by simp) (by simp)⟩

/--
Instance `sumInl_isExpansionOn` / 实例 `sumInl_isExpansionOn`

English:
instance sumInl_isExpansionOn
  signature: (M : Type*) [L.Structure M] [L'.Structure M]
  body: ⟨fun _f _ => rfl, fun _R _ => rfl⟩

中文:
实例 sumInl_isExpansionOn
  签名: (M : 类型) [L.结构 M] [L'.结构 M]
  定义体: ⟨fun _f _ => rfl, fun _R _ => rfl⟩
-/
instance sumInl_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInl : L ->ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

/--
Instance `sumInr_isExpansionOn` / 实例 `sumInr_isExpansionOn`

English:
instance sumInr_isExpansionOn
  signature: (M : Type*) [L.Structure M] [L'.Structure M]
  body: ⟨fun _f _ => rfl, fun _R _ => rfl⟩

@[simp]

中文:
实例 sumInr_isExpansionOn
  签名: (M : 类型) [L.结构 M] [L'.结构 M]
  定义体: ⟨fun _f _ => rfl, fun _R _ => rfl⟩

@[simp]
-/
instance sumInr_isExpansionOn (M : Type*) [L.Structure M] [L'.Structure M] :
    (LHom.sumInr : L' ->ᴸ L.sum L').IsExpansionOn M :=
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

@[simp]
/--
theorem `funMap_sumInl` / 定理 `funMap_sumInl`

English:
theorem funMap_sumInl
  statement: [(L.sum L').Structure M] [(LHom.sumInl : L ->ᴸ L.sum L').IsExpansionOn M] {n}
  proof: (LHom.sumInl : L ->ᴸ L.sum L').map_onFunction f x

@[simp]

中文:
定理 funMap_sumInl
  结论: [(L.求和 L').结构 M] [(L态射.sumInl : L ->ᴸ L.求和 L').是ExpansionOn M] {n}
  证明: (LHom.sumInl : L ->ᴸ L.sum L').map_onFunction f x

@[simp]

Depends on / 依赖: L.sum, LHom.sumInl, map_onFunction, sumInl
-/
theorem funMap_sumInl [(L.sum L').Structure M] [(LHom.sumInl : L ->ᴸ L.sum L').IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n -> M} : @funMap (L.sum L') M _ n (Sum.inl f) x = funMap f x :=
  (LHom.sumInl : L ->ᴸ L.sum L').map_onFunction f x

@[simp]
/--
theorem `funMap_sumInr` / 定理 `funMap_sumInr`

English:
theorem funMap_sumInr
  statement: [(L'.sum L).Structure M] [(LHom.sumInr : L ->ᴸ L'.sum L).IsExpansionOn M] {n}
  proof: (LHom.sumInr : L ->ᴸ L'.sum L).map_onFunction f x

中文:
定理 funMap_sumInr
  结论: [(L'.求和 L).结构 M] [(L态射.sumInr : L ->ᴸ L'.求和 L).是ExpansionOn M] {n}
  证明: (LHom.sumInr : L ->ᴸ L'.sum L).map_onFunction f x

Depends on / 依赖: LHom.sumInr, map_onFunction, sumInr
-/
theorem funMap_sumInr [(L'.sum L).Structure M] [(LHom.sumInr : L ->ᴸ L'.sum L).IsExpansionOn M] {n}
    {f : L.Functions n} {x : Fin n -> M} : @funMap (L'.sum L) M _ n (Sum.inr f) x = funMap f x :=
  (LHom.sumInr : L ->ᴸ L'.sum L).map_onFunction f x

/--
theorem `sumInl_injective` / 定理 `sumInl_injective`

English:
theorem sumInl_injective
  statement: (LHom.sumInl : L ->ᴸ L.sum L').Injective
  proof: ⟨fun h => Sum.inl_injective h, fun h => Sum.inl_injective h⟩

中文:
定理 sumInl_injective
  结论: (L态射.sumInl : L ->ᴸ L.求和 L').单射
  证明: ⟨fun h => Sum.inl_injective h, fun h => Sum.inl_injective h⟩

Depends on / 依赖: Sum.inl_injective, inl_injective
-/
theorem sumInl_injective : (LHom.sumInl : L ->ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inl_injective h, fun h => Sum.inl_injective h⟩

/--
theorem `sumInr_injective` / 定理 `sumInr_injective`

English:
theorem sumInr_injective
  statement: (LHom.sumInr : L' ->ᴸ L.sum L').Injective
  proof: ⟨fun h => Sum.inr_injective h, fun h => Sum.inr_injective h⟩

中文:
定理 sumInr_injective
  结论: (L态射.sumInr : L' ->ᴸ L.求和 L').单射
  证明: ⟨fun h => Sum.inr_injective h, fun h => Sum.inr_injective h⟩

Depends on / 依赖: Sum.inr_injective, inr_injective
-/
theorem sumInr_injective : (LHom.sumInr : L' ->ᴸ L.sum L').Injective :=
  ⟨fun h => Sum.inr_injective h, fun h => Sum.inr_injective h⟩

instance (priority := 100) isExpansionOn_reduct (ϕ : L ->ᴸ L') (M : Type*) [L'.Structure M] :
    @IsExpansionOn L L' ϕ M (ϕ.reduct M) _ :=
  letI := ϕ.reduct M
  ⟨fun _f _ => rfl, fun _R _ => rfl⟩

/--
theorem `Injective.isExpansionOn_default` / 定理 `Injective.isExpansionOn_default`

English:
theorem Injective.isExpansionOn_default
  statement: {ϕ : L ->ᴸ L'}
  proof: by
  let := ϕ.defaultExpansion M
  refine ⟨fun {n} f xs => ?_, fun {n} r xs => ?_⟩
  · have hf : ϕ.onFunction f in Set.range fun f : L.Functions n => ϕ.onFunction f := ⟨f, rfl⟩
    refine (dif_pos hf).trans ?_
    rw [h.onFunction hf.choose_spec]
  · have hr : ϕ.onRelation r in Set.range fun r : L.Relations n => ϕ.onRelation r := ⟨r, rfl⟩
    refine (dif_pos hr).trans ?_
    rw [h.onRelation hr.choose_spec]

中文:
定理 单射.isExpansionOn_default
  结论: {ϕ : L ->ᴸ L'}
  证明: by
  let := ϕ.defaultExpansion M
  refine ⟨fun {n} f xs => ?_, fun {n} r xs => ?_⟩
  · have hf : ϕ.onFunction f in Set.range fun f : L.Functions n => ϕ.onFunction f := ⟨f, rfl⟩
    refine (dif_pos hf).trans ?_
    rw [h.onFunction hf.choose_spec]
  · have hr : ϕ.onRelation r in Set.range fun r : L.Relations n => ϕ.onRelation r := ⟨r, rfl⟩
    refine (dif_pos hr).trans ?_
    rw [h.onRelation hr.choose_spec]

Depends on / 依赖: Functions, L.Functions, L.Relations, Relations, Set.range, choose_spec, defaultExpansion, dif_pos, h.onFunction, h.onRelation, hf.choose_spec, hr.choose_spec, onFunction, onRelation
-/
theorem Injective.isExpansionOn_default {ϕ : L ->ᴸ L'}
    [forall (n) (f : L'.Functions n), Decidable (f in Set.range fun f : L.Functions n => ϕ.onFunction f)]
    [forall (n) (r : L'.Relations n), Decidable (r in Set.range fun r : L.Relations n => ϕ.onRelation r)]
    (h : ϕ.Injective) (M : Type*) [Inhabited M] [L.Structure M] :
    @IsExpansionOn L L' ϕ M _ (ϕ.defaultExpansion M) := by
  let := ϕ.defaultExpansion M
  refine ⟨fun {n} f xs => ?_, fun {n} r xs => ?_⟩
  · have hf : ϕ.onFunction f in Set.range fun f : L.Functions n => ϕ.onFunction f := ⟨f, rfl⟩
    refine (dif_pos hf).trans ?_
    rw [h.onFunction hf.choose_spec]
  · have hr : ϕ.onRelation r in Set.range fun r : L.Relations n => ϕ.onRelation r := ⟨r, rfl⟩
    refine (dif_pos hr).trans ?_
    rw [h.onRelation hr.choose_spec]

end LHom

/--
Definition of `LEquiv` / `LEquiv` 的定义

English:
structure LEquiv
  parameters: (L L' : Language)
  axioms and operations (4):
    - toLHom : L ->ᴸ L'
    - invLHom : L' ->ᴸ L
    - left_inv : invLHom.comp toLHom = LHom.id L
    - right_inv : toLHom.comp invLHom = LHom.id L'

中文:
结构 L等价
  参数: (L L' : Language)
  公理与运算 (4 个):
    - toLHom : L ->ᴸ L'
    - invLHom : L' ->ᴸ L
    - left_inv : invLHom.comp toLHom = L态射.id L
    - right_inv : toLHom.comp invLHom = L态射.id L'
-/
structure LEquiv (L L' : Language) where
  /-- The forward language homomorphism -/
  toLHom : L ->ᴸ L'
  /-- The inverse language homomorphism -/
  invLHom : L' ->ᴸ L
  left_inv : invLHom.comp toLHom = LHom.id L
  right_inv : toLHom.comp invLHom = LHom.id L'

@[inherit_doc] infixl:10 " ≃ᴸ " => LEquiv

-- \^L
namespace LEquiv

variable (L) in
/-- The identity equivalence from a first-order language to itself. -/
@[simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : L ≃ᴸ L
  body: ⟨LHom.id L, LHom.id L, LHom.comp_id _, LHom.comp_id _⟩

中文:
定义 refl
  签名: : L ≃ᴸ L
  定义体: ⟨LHom.id L, LHom.id L, LHom.comp_id _, LHom.comp_id _⟩
-/
protected def refl : L ≃ᴸ L :=
  ⟨LHom.id L, LHom.id L, LHom.comp_id _, LHom.comp_id _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (L ≃ᴸ L)
  body: ⟨LEquiv.refl L⟩

中文:
实例 :
  签名: 可居 (L ≃ᴸ L)
  定义体: ⟨LEquiv.refl L⟩

Depends on / 依赖: LEquiv, LEquiv.refl
-/
instance : Inhabited (L ≃ᴸ L) :=
  ⟨LEquiv.refl L⟩

variable {L'' : Language} (e' : L' ≃ᴸ L'') (e : L ≃ᴸ L')

/-- The inverse of an equivalence of first-order languages. -/
@[simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : L' ≃ᴸ L
  body: ⟨e.invLHom, e.toLHom, e.right_inv, e.left_inv⟩

中文:
定义 symm
  签名: : L' ≃ᴸ L
  定义体: ⟨e.invLHom, e.toLHom, e.right_inv, e.left_inv⟩
-/
protected def symm : L' ≃ᴸ L :=
  ⟨e.invLHom, e.toLHom, e.right_inv, e.left_inv⟩

/-- The composition of equivalences of first-order languages. -/
@[simps, trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'')
  body: ⟨e'.toLHom.comp e.toLHom, e.invLHom.comp e'.invLHom, by
    rw [LHom.comp_assoc]; rw [← LHom.comp_assoc e'.invLHom]; rw [e'.left_inv]; rw [LHom.id_comp]; rw [e.left_inv], by
    rw [LHom.comp_assoc]; rw [← LHom.comp_assoc e.toLHom]; rw [e.right_inv]; rw [LHom.id_comp]; rw [e'.right_inv]⟩

中文:
定义 trans
  签名: (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'')
  定义体: ⟨e'.toLHom.comp e.toLHom, e.invLHom.comp e'.invLHom, by
    rw [LHom.comp_assoc]; rw [← LHom.comp_assoc e'.invLHom]; rw [e'.left_inv]; rw [LHom.id_comp]; rw [e.left_inv], by
    rw [LHom.comp_assoc]; rw [← LHom.comp_assoc e.toLHom]; rw [e.right_inv]; rw [LHom.id_comp]; rw [e'.right_inv]⟩
-/
protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
  ⟨e'.toLHom.comp e.toLHom, e.invLHom.comp e'.invLHom, by
    rw [LHom.comp_assoc]; rw [← LHom.comp_assoc e'.invLHom]; rw [e'.left_inv]; rw [LHom.id_comp]; rw [e.left_inv], by
    rw [LHom.comp_assoc]; rw [← LHom.comp_assoc e.toLHom]; rw [e.right_inv]; rw [LHom.id_comp]; rw [e'.right_inv]⟩

end LEquiv

section ConstantsOn

variable (α : Type u')

/-- The type of functions for a language consisting only of constant symbols. -/
@[simp]
/--
Definition of `constantsOnFunc` / `constantsOnFunc` 的定义

English:
definition constantsOnFunc
  signature: : Nat -> Type u'

中文:
定义 constantsOnFunc
  签名: : 自然数 -> 类型u'
-/
def constantsOnFunc : Nat -> Type u'
  | 0 => α
  | (_ + 1) => PEmpty

/-- A language with constants indexed by a type. -/
@[simps]
/--
Definition of `constantsOn` / `constantsOn` 的定义

English:
definition constantsOn
  signature: : Language.{u', 0}
  body: ⟨constantsOnFunc α, fun _ => Empty⟩
deriving IsAlgebraic

中文:
定义 constantsOn
  签名: : Language.{u', 0}
  定义体: ⟨constantsOnFunc α, fun _ => Empty⟩
deriving IsAlgebraic

Depends on / 依赖: constantsOnFunc
-/
def constantsOn : Language.{u', 0} := ⟨constantsOnFunc α, fun _ => Empty⟩
deriving IsAlgebraic

variable {α}

/--
theorem `constantsOn_constants` / 定理 `constantsOn_constants`

English:
theorem constantsOn_constants
  statement: (constantsOn α).Constants = α
  proof: rfl

中文:
定理 constantsOn_constants
  结论: (constantsOn α).Constants = α
  证明: rfl
-/
theorem constantsOn_constants : (constantsOn α).Constants = α :=
  rfl

/--
Instance `isEmpty_functions_constantsOn_succ` / 实例 `isEmpty_functions_constantsOn_succ`

English:
instance isEmpty_functions_constantsOn_succ
  signature: {n : Nat}
  body: inferInstanceAs (IsEmpty PEmpty)

中文:
实例 isEmpty_functions_constantsOn_succ
  签名: {n : 自然数}
  定义体: inferInstanceAs (IsEmpty PEmpty)

Depends on / 依赖: IsEmpty, PEmpty
-/
instance isEmpty_functions_constantsOn_succ {n : Nat} : IsEmpty ((constantsOn α).Functions (n + 1)) :=
  inferInstanceAs (IsEmpty PEmpty)

/--
Instance `isRelational_constantsOn` / 实例 `isRelational_constantsOn`

English:
instance isRelational_constantsOn
  signature: [_ie : IsEmpty α]
  body: fun n => Nat.casesOn n _ie inferInstance

中文:
实例 isRelational_constantsOn
  签名: [_ie : 是空 α]
  定义体: fun n => Nat.casesOn n _ie inferInstance

Depends on / 依赖: Nat.casesOn, casesOn
-/
instance isRelational_constantsOn [_ie : IsEmpty α] : IsRelational (constantsOn α) :=
  fun n => Nat.casesOn n _ie inferInstance

/--
theorem `card_constantsOn` / 定理 `card_constantsOn`

English:
theorem card_constantsOn
  statement: (constantsOn α).card = #α
  proof: by
  simp [card_eq_card_functions_add_card_relations, sum_nat_eq_add_sum_succ]

中文:
定理 card_constantsOn
  结论: (constantsOn α).card = #α
  证明: by
  simp [card_eq_card_functions_add_card_relations, sum_nat_eq_add_sum_succ]

Depends on / 依赖: card_eq_card_functions_add_card_relations, sum_nat_eq_add_sum_succ
-/
theorem card_constantsOn : (constantsOn α).card = #α := by
  simp [card_eq_card_functions_add_card_relations, sum_nat_eq_add_sum_succ]

/-- Gives a `constantsOn α` structure to a type by assigning each constant a value. -/
@[instance_reducible]
/--
Definition of `constantsOn.structure` / `constantsOn.structure` 的定义

English:
definition constantsOn.structure
  signature: (f : α -> M)
  body: fun {n} c _ =>
    match n, c with
    | 0, c => f c

中文:
定义 constantsOn.structure
  签名: (f : α -> M)
  定义体: fun {n} c _ =>
    match n, c with
    | 0, c => f c
-/
def constantsOn.structure (f : α -> M) : (constantsOn α).Structure M where
  funMap := fun {n} c _ =>
    match n, c with
    | 0, c => f c

variable {β : Type v'}

/--
Definition of `LHom.constantsOnMap` / `LHom.constantsOnMap` 的定义

English:
definition LHom.constantsOnMap
  signature: (f : α -> β)
  body: fun {n} c =>
    match n, c with
    | 0, c => f c

中文:
定义 L态射.constantsOnMap
  签名: (f : α -> β)
  定义体: fun {n} c =>
    match n, c with
    | 0, c => f c
-/
def LHom.constantsOnMap (f : α -> β) : constantsOn α ->ᴸ constantsOn β where
  onFunction := fun {n} c =>
    match n, c with
    | 0, c => f c

/--
theorem `constantsOnMap_isExpansionOn` / 定理 `constantsOnMap_isExpansionOn`

English:
theorem constantsOnMap_isExpansionOn
  given: {f : α -> β} {fα : α -> M} {fβ : β -> M} (h : fβ ∘ f = fα)
  proof: by
  let := constantsOn.structure fα
  let := constantsOn.structure fβ
  exact
    ⟨fun {n} => Nat.casesOn n (fun F _x => (congr_fun h F :)) fun n F => isEmptyElim F, fun R =>
      isEmptyElim R⟩

中文:
定理 constantsOnMap_isExpansionOn
  条件: {f : α -> β} {fα : α -> M} {fβ : β -> M} (h : fβ ∘ f = fα)
  证明: by
  let := constantsOn.structure fα
  let := constantsOn.structure fβ
  exact
    ⟨fun {n} => Nat.casesOn n (fun F _x => (congr_fun h F :)) fun n F => isEmptyElim F, fun R =>
      isEmptyElim R⟩

Depends on / 依赖: Nat.casesOn, casesOn, congr_fun, constantsOn, constantsOn.structure, isEmptyElim, structure
-/
theorem constantsOnMap_isExpansionOn {f : α -> β} {fα : α -> M} {fβ : β -> M} (h : fβ ∘ f = fα) :
    @LHom.IsExpansionOn _ _ (LHom.constantsOnMap f) M (constantsOn.structure fα)
      (constantsOn.structure fβ) := by
  let := constantsOn.structure fα
  let := constantsOn.structure fβ
  exact
    ⟨fun {n} => Nat.casesOn n (fun F _x => (congr_fun h F :)) fun n F => isEmptyElim F, fun R =>
      isEmptyElim R⟩

end ConstantsOn

section WithConstants

variable (L)

section

variable (α : Type w')

/--
Definition of `withConstants` / `withConstants` 的定义

English:
definition withConstants
  signature: : Language.{max u w', v}
  body: L.sum (constantsOn α)

@[inherit_doc FirstOrder.Language.withConstants]
scoped[FirstOrder] notation:max L "[[" α "]]" => Language.withConstants L α

@[simp]

中文:
定义 withConstants
  签名: : Language.{最大值 u w', v}
  定义体: L.sum (constantsOn α)

@[inherit_doc FirstOrder.Language.withConstants]
scoped[FirstOrder] notation:max L "[[" α "]]" => Language.withConstants L α

@[simp]

Depends on / 依赖: L.sum, constantsOn
-/
def withConstants : Language.{max u w', v} :=
  L.sum (constantsOn α)

@[inherit_doc FirstOrder.Language.withConstants]
scoped[FirstOrder] notation:max L "[[" α "]]" => Language.withConstants L α

@[simp]
/--
theorem `card_withConstants` / 定理 `card_withConstants`

English:
theorem card_withConstants
  proof: by
  rw [withConstants]; rw [card_sum]; rw [card_constantsOn]

中文:
定理 card_withConstants
  证明: by
  rw [withConstants]; rw [card_sum]; rw [card_constantsOn]

Depends on / 依赖: card_constantsOn, card_sum, withConstants
-/
theorem card_withConstants :
    L[[α]].card = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} #α := by
  rw [withConstants]; rw [card_sum]; rw [card_constantsOn]

/-- The language map adding constants. -/
@[simps!]
/--
Definition of `lhomWithConstants` / `lhomWithConstants` 的定义

English:
definition lhomWithConstants
  signature: : L ->ᴸ L[[α]]
  body: LHom.sumInl

中文:
定义 lhomWithConstants
  签名: : L ->ᴸ L[[α]]
  定义体: LHom.sumInl

Depends on / 依赖: LHom.sumInl, sumInl
-/
def lhomWithConstants : L ->ᴸ L[[α]] :=
  LHom.sumInl

/--
theorem `lhomWithConstants_injective` / 定理 `lhomWithConstants_injective`

English:
theorem lhomWithConstants_injective
  statement: (L.lhomWithConstants α).Injective
  proof: LHom.sumInl_injective

中文:
定理 lhomWithConstants_injective
  结论: (L.lhomWithConstants α).单射
  证明: LHom.sumInl_injective

Depends on / 依赖: LHom.sumInl_injective, sumInl_injective
-/
theorem lhomWithConstants_injective : (L.lhomWithConstants α).Injective :=
  LHom.sumInl_injective

variable {α}

/--
Definition of `con` / `con` 的定义

English:
definition con
  signature: (a : α)
  body: Sum.inr a

中文:
定义 con
  签名: (a : α)
  定义体: Sum.inr a
-/
protected def con (a : α) : L[[α]].Constants :=
  Sum.inr a

variable {L} (α)

/--
Definition of `LHom.addConstants` / `LHom.addConstants` 的定义

English:
definition LHom.addConstants
  signature: {L' : Language} (φ : L ->ᴸ L')
  body: φ.sumMap (LHom.id _)

中文:
定义 L态射.addConstants
  签名: {L' : Language} (φ : L ->ᴸ L')
  定义体: φ.sumMap (LHom.id _)

Depends on / 依赖: LHom.id, sumMap
-/
def LHom.addConstants {L' : Language} (φ : L ->ᴸ L') : L[[α]] ->ᴸ L'[[α]] :=
  φ.sumMap (LHom.id _)

/--
Instance `paramsStructure` / 实例 `paramsStructure`

English:
instance paramsStructure
  signature: (A : Set α)
  body: constantsOn.structure (↑)

中文:
实例 paramsStructure
  签名: (A : 集合 α)
  定义体: constantsOn.structure (↑)

Depends on / 依赖: constantsOn, constantsOn.structure, structure
-/
instance paramsStructure (A : Set α) : (constantsOn A).Structure α :=
  constantsOn.structure (↑)

variable (L)

set_option backward.isDefEq.respectTransparency false in
/-- The language map removing an empty constant set. -/
@[simps]
/--
Definition of `LEquiv.addEmptyConstants` / `LEquiv.addEmptyConstants` 的定义

English:
definition LEquiv.addEmptyConstants
  signature: [ie : IsEmpty α]
  body: lhomWithConstants L α
  invLHom := LHom.sumElim (LHom.id L) (LHom.ofIsEmpty (constantsOn α) L)
  left_inv := by rw [lhomWithConstants, LHom.sumElim_comp_inl]
  right_inv := by
    simp only [LHom.comp_sumElim, lhomWithConstants, LHom.comp_id]
    exact _root_.trans (congr rfl (Subsingleton.elim _ _)) LHom.sumElim_inl_inr

中文:
定义 L等价.addEmptyConstants
  签名: [ie : 是空 α]
  定义体: lhomWithConstants L α
  invLHom := LHom.sumElim (LHom.id L) (LHom.ofIsEmpty (constantsOn α) L)
  left_inv := by rw [lhomWithConstants, LHom.sumElim_comp_inl]
  right_inv := by
    simp only [LHom.comp_sumElim, lhomWithConstants, LHom.comp_id]
    exact _root_.trans (congr rfl (Subsingleton.elim _ _)) LHom.sumElim_inl_inr

Depends on / 依赖: lhomWithConstants
-/
def LEquiv.addEmptyConstants [ie : IsEmpty α] : L ≃ᴸ L[[α]] where
  toLHom := lhomWithConstants L α
  invLHom := LHom.sumElim (LHom.id L) (LHom.ofIsEmpty (constantsOn α) L)
  left_inv := by rw [lhomWithConstants, LHom.sumElim_comp_inl]
  right_inv := by
    simp only [LHom.comp_sumElim, lhomWithConstants, LHom.comp_id]
    exact _root_.trans (congr rfl (Subsingleton.elim _ _)) LHom.sumElim_inl_inr

variable {α} {β : Type*}

@[simp]
/--
theorem `withConstants_funMap_sumInl` / 定理 `withConstants_funMap_sumInl`

English:
theorem withConstants_funMap_sumInl
  statement: [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
  proof: (lhomWithConstants L α).map_onFunction f x

@[simp]

中文:
定理 withConstants_funMap_sumInl
  结论: [L[[α]].结构 M] [(lhomWithConstants L α).是ExpansionOn M]
  证明: (lhomWithConstants L α).map_onFunction f x

@[simp]

Depends on / 依赖: lhomWithConstants, map_onFunction
-/
theorem withConstants_funMap_sumInl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {f : L.Functions n} {x : Fin n -> M} : @funMap L[[α]] M _ n (Sum.inl f) x = funMap f x :=
  (lhomWithConstants L α).map_onFunction f x

@[simp]
/--
theorem `withConstants_relMap_sumInl` / 定理 `withConstants_relMap_sumInl`

English:
theorem withConstants_relMap_sumInl
  statement: [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
  proof: (lhomWithConstants L α).map_onRelation R x

中文:
定理 withConstants_relMap_sumInl
  结论: [L[[α]].结构 M] [(lhomWithConstants L α).是ExpansionOn M]
  证明: (lhomWithConstants L α).map_onRelation R x

Depends on / 依赖: lhomWithConstants, map_onRelation
-/
theorem withConstants_relMap_sumInl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {R : L.Relations n} {x : Fin n -> M} : @RelMap L[[α]] M _ n (Sum.inl R) x = RelMap R x :=
  (lhomWithConstants L α).map_onRelation R x

/--
Definition of `lhomWithConstantsMap` / `lhomWithConstantsMap` 的定义

English:
definition lhomWithConstantsMap
  signature: (f : α -> β)
  body: LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)

@[simp]

中文:
定义 lhomWithConstantsMap
  签名: (f : α -> β)
  定义体: LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)

@[simp]

Depends on / 依赖: LHom.constantsOnMap, LHom.id, LHom.sumMap, constantsOnMap, sumMap
-/
def lhomWithConstantsMap (f : α -> β) : L[[α]] ->ᴸ L[[β]] :=
  LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)

@[simp]
/--
theorem `LHom.map_constants_comp_sumInl` / 定理 `LHom.map_constants_comp_sumInl`

English:
theorem LHom.map_constants_comp_sumInl
  given: {f : α -> β}
  proof: by ext <;> rfl

中文:
定理 L态射.map_constants_comp_sumInl
  条件: {f : α -> β}
  证明: by ext <;> rfl
-/
theorem LHom.map_constants_comp_sumInl {f : α -> β} :
    (L.lhomWithConstantsMap f).comp LHom.sumInl = L.lhomWithConstants β := by ext <;> rfl

end

open FirstOrder

variable (α : Type*) [(constantsOn α).Structure M]

/--
Instance `withConstantsStructure` / 实例 `withConstantsStructure`

English:
instance withConstantsStructure
  signature: : L[[α]].Structure M
  body: inferInstanceAs (L.sum _).Structure M

中文:
实例 withConstantsStructure
  签名: : L[[α]].结构 M
  定义体: inferInstanceAs (L.sum _).Structure M

Depends on / 依赖: L.sum, Structure
-/
instance withConstantsStructure : L[[α]].Structure M :=
inferInstanceAs (L.sum _).Structure M

/--
Instance `constantsOnSelfStructure` / 实例 `constantsOnSelfStructure`

English:
instance constantsOnSelfStructure
  signature: : (constantsOn M).Structure M
  body: fast_instance% constantsOn.structure id

中文:
实例 constantsOnSelfStructure
  签名: : (constantsOn M).结构 M
  定义体: fast_instance% constantsOn.structure id

Depends on / 依赖: constantsOn, constantsOn.structure, fast_instance, structure
-/
instance constantsOnSelfStructure : (constantsOn M).Structure M :=
  fast_instance% constantsOn.structure id

/--
Instance `withConstantsSelfStructure` / 实例 `withConstantsSelfStructure`

English:
instance withConstantsSelfStructure
  signature: : L[[M]].Structure M
  body: inferInstance

中文:
实例 withConstantsSelfStructure
  签名: : L[[M]].结构 M
  定义体: inferInstance
-/
instance withConstantsSelfStructure : L[[M]].Structure M := inferInstance

/--
Instance `withConstants_self_expansion` / 实例 `withConstants_self_expansion`

English:
instance withConstants_self_expansion
  signature: : (lhomWithConstants L M).IsExpansionOn M
  body: ⟨fun _ _ => rfl, fun _ _ => rfl⟩

中文:
实例 withConstants_self_expansion
  签名: : (lhomWithConstants L M).是ExpansionOn M
  定义体: ⟨fun _ _ => rfl, fun _ _ => rfl⟩
-/
instance withConstants_self_expansion : (lhomWithConstants L M).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/--
Instance `withConstants_expansion` / 实例 `withConstants_expansion`

English:
instance withConstants_expansion
  signature: : (L.lhomWithConstants α).IsExpansionOn M
  body: ⟨fun _ _ => rfl, fun _ _ => rfl⟩

中文:
实例 withConstants_expansion
  签名: : (L.lhomWithConstants α).是ExpansionOn M
  定义体: ⟨fun _ _ => rfl, fun _ _ => rfl⟩
-/
instance withConstants_expansion : (L.lhomWithConstants α).IsExpansionOn M :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/--
Instance `addEmptyConstants_is_expansion_on'` / 实例 `addEmptyConstants_is_expansion_on'`

English:
instance addEmptyConstants_is_expansion_on'
  signature: :
  body: L.withConstants_expansion _

中文:
实例 addEmptyConstants_is_expansion_on'
  签名: :
  定义体: L.withConstants_expansion _

Depends on / 依赖: L.withConstants_expansion, withConstants_expansion
-/
instance addEmptyConstants_is_expansion_on' :
    (LEquiv.addEmptyConstants L (∅ : Set M)).toLHom.IsExpansionOn M :=
  L.withConstants_expansion _

/--
Instance `addEmptyConstants_symm_isExpansionOn` / 实例 `addEmptyConstants_symm_isExpansionOn`

English:
instance addEmptyConstants_symm_isExpansionOn
  signature: :
  body: LHom.sumElim_isExpansionOn _ _ _

中文:
实例 addEmptyConstants_symm_isExpansionOn
  签名: :
  定义体: LHom.sumElim_isExpansionOn _ _ _

Depends on / 依赖: LHom.sumElim_isExpansionOn, sumElim_isExpansionOn
-/
instance addEmptyConstants_symm_isExpansionOn :
    (LEquiv.addEmptyConstants L (∅ : Set M)).symm.toLHom.IsExpansionOn M :=
  LHom.sumElim_isExpansionOn _ _ _

/--
Instance `addConstants_expansion` / 实例 `addConstants_expansion`

English:
instance addConstants_expansion
  signature: {L' : Language} [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M]
  body: LHom.sumMap_isExpansionOn _ _ M

中文:
实例 addConstants_expansion
  签名: {L' : Language} [L'.结构 M] (φ : L ->ᴸ L') [φ.是ExpansionOn M]
  定义体: LHom.sumMap_isExpansionOn _ _ M

Depends on / 依赖: LHom.sumMap_isExpansionOn, sumMap_isExpansionOn
-/
instance addConstants_expansion {L' : Language} [L'.Structure M] (φ : L ->ᴸ L') [φ.IsExpansionOn M] :
    (φ.addConstants α).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ M

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `withConstants_funMap_sumInr` / 定理 `withConstants_funMap_sumInr`

English:
theorem withConstants_funMap_sumInr
  given: {a : α} {x : Fin 0 -> M}
  proof: by
  rw [Unique.eq_default x]
  exact (LHom.sumInr : constantsOn α ->ᴸ L.sum _).map_onFunction _ _

中文:
定理 withConstants_funMap_sumInr
  条件: {a : α} {x : 有限集 0 -> M}
  证明: by
  rw [Unique.eq_default x]
  exact (LHom.sumInr : constantsOn α ->ᴸ L.sum _).map_onFunction _ _

Depends on / 依赖: L.sum, LHom.sumInr, Unique, Unique.eq_default, constantsOn, eq_default, map_onFunction, sumInr
-/
theorem withConstants_funMap_sumInr {a : α} {x : Fin 0 -> M} :
    @funMap L[[α]] M _ 0 (Sum.inr a : L[[α]].Functions 0) x = L.con a := by
  rw [Unique.eq_default x]
  exact (LHom.sumInr : constantsOn α ->ᴸ L.sum _).map_onFunction _ _

variable {α} (A : Set M)

@[simp]
/--
theorem `coe_con` / 定理 `coe_con`

English:
theorem coe_con
  given: {a : A}
  statement: (L.con a : M) = a
  proof: rfl

中文:
定理 coe_con
  条件: {a : A}
  结论: (L.con a : M) = a
  证明: rfl
-/
theorem coe_con {a : A} : (L.con a : M) = a :=
  rfl

variable {A} {B : Set M} (h : A subseteq B)

/--
Instance `constantsOnMap_inclusion_isExpansionOn` / 实例 `constantsOnMap_inclusion_isExpansionOn`

English:
instance constantsOnMap_inclusion_isExpansionOn
  signature: :
  body: constantsOnMap_isExpansionOn rfl

中文:
实例 constantsOnMap_inclusion_isExpansionOn
  签名: :
  定义体: constantsOnMap_isExpansionOn rfl

Depends on / 依赖: constantsOnMap_isExpansionOn
-/
instance constantsOnMap_inclusion_isExpansionOn :
    (LHom.constantsOnMap (Set.inclusion h)).IsExpansionOn M :=
  constantsOnMap_isExpansionOn rfl

/--
Instance `map_constants_inclusion_isExpansionOn` / 实例 `map_constants_inclusion_isExpansionOn`

English:
instance map_constants_inclusion_isExpansionOn
  signature: :
  body: LHom.sumMap_isExpansionOn _ _ _

中文:
实例 map_constants_inclusion_isExpansionOn
  签名: :
  定义体: LHom.sumMap_isExpansionOn _ _ _

Depends on / 依赖: LHom.sumMap_isExpansionOn, sumMap_isExpansionOn
-/
instance map_constants_inclusion_isExpansionOn :
    (L.lhomWithConstantsMap (Set.inclusion h)).IsExpansionOn M :=
  LHom.sumMap_isExpansionOn _ _ _

variable {L} (A) {N : Type w'} [L.Structure N] (f : M ↪[L] N)

/-- Type synonym for `N` used to equip it with an `L[[A]]`-structure where the new constants on `A`
are interpreted via the embedding `f`. -/
@[nolint unusedArguments]
/--
Definition of `Embedding.withConstants` / `Embedding.withConstants` 的定义

English:
definition Embedding.withConstants
  signature: (_f : M ↪[L] N) (_A : Set M)
  body: N
deriving L.Structure

中文:
定义 嵌入.withConstants
  签名: (_f : M ↪[L] N) (_A : 集合 M)
  定义体: N
deriving L.Structure
-/
def Embedding.withConstants (_f : M ↪[L] N) (_A : Set M) : Type w' := N
deriving L.Structure

instance (f : M ↪[L] N) : (constantsOn A).Structure (f.withConstants A) :=
  fast_instance% constantsOn.structure fun a => f a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: L[[A]].Structure (f.withConstants A)
  body: inferInstance

中文:
实例 :
  签名: L[[A]].结构 (f.withConstants A)
  定义体: inferInstance
-/
instance : L[[A]].Structure (f.withConstants A) := inferInstance

/--
Definition of `Embedding.liftWithConstants` / `Embedding.liftWithConstants` 的定义

English:
definition Embedding.liftWithConstants
  signature: :
  body: by
  refine ⟨f.toEmbedding, ?_, ?_⟩
  · intro n g x
    cases g with
    | inl g => exact f.map_fun' g x
    | inr c =>
      cases n with
      | zero => rfl
      | succ n => exact isEmptyElim c
  · intro n R x
    cases R with
    | inl R => exact f.map_rel' R x
    | inr r => exact isEmptyElim r

中文:
定义 嵌入.liftWithConstants
  签名: :
  定义体: by
  refine ⟨f.toEmbedding, ?_, ?_⟩
  · intro n g x
    cases g with
    | inl g => exact f.map_fun' g x
    | inr c =>
      cases n with
      | zero => rfl
      | succ n => exact isEmptyElim c
  · intro n R x
    cases R with
    | inl R => exact f.map_rel' R x
    | inr r => exact isEmptyElim r

Depends on / 依赖: f.map_fun, f.map_rel, f.toEmbedding, isEmptyElim, map_fun, map_rel, toEmbedding
-/
def Embedding.liftWithConstants :
    M ↪[L[[A]]] f.withConstants A := by
  refine ⟨f.toEmbedding, ?_, ?_⟩
  · intro n g x
    cases g with
    | inl g => exact f.map_fun' g x
    | inr c =>
      cases n with
      | zero => rfl
      | succ n => exact isEmptyElim c
  · intro n R x
    cases R with
    | inl R => exact f.map_rel' R x
    | inr r => exact isEmptyElim r

end WithConstants

end Language

end FirstOrder
