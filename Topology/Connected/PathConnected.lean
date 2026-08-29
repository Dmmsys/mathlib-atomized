/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Path

/-!
# Path connectedness

Continuing from `Mathlib/Topology/Path.lean`, this file defines path components and path-connected
spaces.

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Joined (x y : X)` means there is a path between `x` and `y`.
* `Joined.somePath (h : Joined x y)` selects some path between two points `x` and `y`.
* `pathComponent (x : X)` is the set of points joined to `x`.
* `PathConnectedSpace X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : Set X`.

* `JoinedIn F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `JoinedIn.somePath (h : JoinedIn F x y)` selects a path from `x` to `y` inside `F`.
* `pathComponentIn F (x : X)` is the set of points joined to `x` in `F`.
* `IsPathConnected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.

## Main theorems

* `Joined` is an equivalence relation, while `JoinedIn F` is at least symmetric and transitive.

One can link the absolute and relative version in two directions, using `(univ : Set X)` or the
subtype `↥F`.

* `pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X)`
* `isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace ↥F`

Furthermore, it is shown that continuous images and quotients of path-connected sets/spaces are
path-connected, and that every path-connected set/space is also connected. (See
`Counterexamples.TopologistsSineCurve` for an example of a set in `ℝ × ℝ` that is connected but not
path-connected.)
-/

@[expose] public section

noncomputable section

open Topology Filter unitInterval Set Function Pointwise Fin

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Being joined by a path -/


/--
Definition of `Joined` / `Joined` 的定义

English:
definition Joined
  signature: (x y : X)
  body: Nonempty (Path x y)

@[refl]

中文:
定义 Joined
  签名: (x y : X)
  定义体: Nonempty (Path x y)

@[refl]

Depends on / 依赖: Nonempty
-/
def Joined (x y : X) : Prop :=
  Nonempty (Path x y)

@[refl]
/--
theorem `Joined.refl` / 定理 `Joined.refl`

English:
theorem Joined.refl
  given: (x : X)
  statement: Joined x x
  proof: ⟨Path.refl x⟩

中文:
定理 Joined.refl
  条件: (x : X)
  结论: Joined x x
  证明: ⟨Path.refl x⟩

Depends on / 依赖: Path.refl
-/
theorem Joined.refl (x : X) : Joined x x :=
  ⟨Path.refl x⟩

/--
Definition of `Joined.somePath` / `Joined.somePath` 的定义

English:
definition Joined.somePath
  signature: (h : Joined x y)
  body: Nonempty.some h

@[symm]

中文:
定义 Joined.somePath
  签名: (h : Joined x y)
  定义体: Nonempty.some h

@[symm]

Depends on / 依赖: Nonempty, Nonempty.some
-/
def Joined.somePath (h : Joined x y) : Path x y :=
  Nonempty.some h

@[symm]
/--
theorem `Joined.symm` / 定理 `Joined.symm`

English:
theorem Joined.symm
  given: {x y : X} (h : Joined x y)
  statement: Joined y x
  proof: ⟨h.somePath.symm⟩

@[trans]

中文:
定理 Joined.symm
  条件: {x y : X} (h : Joined x y)
  结论: Joined y x
  证明: ⟨h.somePath.symm⟩

@[trans]

Depends on / 依赖: h.somePath.symm, somePath
-/
theorem Joined.symm {x y : X} (h : Joined x y) : Joined y x :=
  ⟨h.somePath.symm⟩

@[trans]
/--
theorem `Joined.trans` / 定理 `Joined.trans`

English:
theorem Joined.trans
  given: {x y z : X} (hxy : Joined x y) (hyz : Joined y z)
  statement: Joined x z
  proof: ⟨hxy.somePath.trans hyz.somePath⟩

中文:
定理 Joined.trans
  条件: {x y z : X} (hxy : Joined x y) (hyz : Joined y z)
  结论: Joined x z
  证明: ⟨hxy.somePath.trans hyz.somePath⟩

Depends on / 依赖: hxy.somePath.trans, hyz.somePath, somePath
-/
theorem Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x z :=
  ⟨hxy.somePath.trans hyz.somePath⟩

/--
theorem `Joined.map` / 定理 `Joined.map`

English:
theorem Joined.map
  given: {x y : X} {f : X -> Y} (h : Joined x y) (hf : Continuous f)
  proof: ⟨h.somePath.map hf⟩

@[to_additive]

中文:
定理 Joined.map
  条件: {x y : X} {f : X -> Y} (h : Joined x y) (hf : 连续 f)
  证明: ⟨h.somePath.map hf⟩

@[to_additive]

Depends on / 依赖: h.somePath.map, somePath
-/
theorem Joined.map {x y : X} {f : X -> Y} (h : Joined x y) (hf : Continuous f) :
    Joined (f x) (f y) :=
  ⟨h.somePath.map hf⟩

@[to_additive]
/--
theorem `Joined.mul` / 定理 `Joined.mul`

English:
theorem Joined.mul
  statement: {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
  proof: ⟨hs.somePath.mul ht.somePath⟩

@[to_additive]

中文:
定理 Joined.mul
  结论: {M : 类型} [乘法 M] [拓扑空间 M] [连续乘法 M]
  证明: ⟨hs.somePath.mul ht.somePath⟩

@[to_additive]

Depends on / 依赖: hs.somePath.mul, ht.somePath, somePath
-/
theorem Joined.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
    {a b c d : M} (hs : Joined a b) (ht : Joined c d) : Joined (a * c) (b * d) :=
  ⟨hs.somePath.mul ht.somePath⟩

@[to_additive]
/--
theorem `Joined.listProd` / 定理 `Joined.listProd`

English:
theorem Joined.listProd
  statement: {M : Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M]
  proof: by
  induction h with
  | nil => rfl
  | cons h₁ _ h₂ => exact h₁.mul h₂

@[to_additive]

中文:
定理 Joined.listProd
  结论: {M : 类型} [MulOne类 M] [拓扑空间 M] [连续乘法 M]
  证明: by
  induction h with
  | nil => rfl
  | cons h₁ _ h₂ => exact h₁.mul h₂

@[to_additive]
-/
theorem Joined.listProd {M : Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M]
    {l l' : List M} (h : List.Forall₂ Joined l l') :
    Joined l.prod l'.prod := by
  induction h with
  | nil => rfl
  | cons h₁ _ h₂ => exact h₁.mul h₂

@[to_additive]
/--
theorem `Joined.inv` / 定理 `Joined.inv`

English:
theorem Joined.inv
  statement: {G : Type*} [Inv G] [TopologicalSpace G] [ContinuousInv G]
  proof: ⟨h.somePath.inv⟩

中文:
定理 Joined.inv
  结论: {G : 类型} [取逆 G] [拓扑空间 G] [连续取逆 G]
  证明: ⟨h.somePath.inv⟩

Depends on / 依赖: h.somePath.inv, somePath
-/
theorem Joined.inv {G : Type*} [Inv G] [TopologicalSpace G] [ContinuousInv G]
    {x y : G} (h : Joined x y) : Joined x⁻¹ y⁻¹ :=
  ⟨h.somePath.inv⟩

variable (X)

/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
@[instance_reducible]
/--
Definition of `pathSetoid` / `pathSetoid` 的定义

English:
definition pathSetoid
  signature: : Setoid X where
  body: Joined
  iseqv := Equivalence.mk Joined.refl Joined.symm Joined.trans

中文:
定义 pathSetoid
  签名: : 集合等价关系 X where
  定义体: Joined
  iseqv := Equivalence.mk Joined.refl Joined.symm Joined.trans

Depends on / 依赖: Joined
-/
def pathSetoid : Setoid X where
  r := Joined
  iseqv := Equivalence.mk Joined.refl Joined.symm Joined.trans

/--
Definition of `ZerothHomotopy` / `ZerothHomotopy` 的定义

English:
definition ZerothHomotopy
  body: Quotient (pathSetoid X)

中文:
定义 ZerothHomotopy
  定义体: Quotient (pathSetoid X)

Depends on / 依赖: Quotient, pathSetoid
-/
def ZerothHomotopy :=
  Quotient (pathSetoid X)

namespace ZerothHomotopy

variable {X}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : X)
  body: Quotient.mk _ x

中文:
定义 mk
  签名: (x : X)
  定义体: Quotient.mk _ x

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk (x : X) : ZerothHomotopy X := Quotient.mk _ x

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  statement: Function.Surjective (mk (X := X))
  proof: by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

@[elab_as_elim, induction_eliminator, cases_eliminator]

中文:
引理 mk_surjective
  结论: 函数.满射 (mk (X := X))
  证明: by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

@[elab_as_elim, induction_eliminator, cases_eliminator]
-/
lemma mk_surjective : Function.Surjective (mk (X := X)) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
lemma `rec` / 引理 `rec`

English:
lemma rec
  statement: {motive : ZerothHomotopy X -> Prop}
  proof: by
  obtain ⟨x, rfl⟩ := mk_surjective x
  exact mk x

中文:
引理 rec
  结论: {motive : ZerothHomotopy X -> 命题}
  证明: by
  obtain ⟨x, rfl⟩ := mk_surjective x
  exact mk x

Depends on / 依赖: mk_surjective
-/
lemma rec {motive : ZerothHomotopy X -> Prop}
    (mk : forall (x : X), motive (.mk x)) (x : ZerothHomotopy X) :
    motive x := by
  obtain ⟨x, rfl⟩ := mk_surjective x
  exact mk x

/--
lemma `sound` / 引理 `sound`

English:
lemma sound
  given: {x y : X} (p : Path x y)
  statement: mk x = mk y
  proof: Quotient.sound ⟨p⟩

中文:
引理 sound
  条件: {x y : X} (p : 道路 x y)
  结论: mk x = mk y
  证明: Quotient.sound ⟨p⟩

Depends on / 依赖: Quotient, Quotient.sound
-/
lemma sound {x y : X} (p : Path x y) : mk x = mk y :=
  Quotient.sound ⟨p⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace ZerothHomotopy X
  body: inferInstanceAs TopologicalSpace Quotient _

中文:
实例 :
  签名: 拓扑空间 ZerothHomotopy X
  定义体: inferInstanceAs TopologicalSpace Quotient _

Depends on / 依赖: Quotient, TopologicalSpace
-/
instance : TopologicalSpace ZerothHomotopy X :=
inferInstanceAs TopologicalSpace Quotient _

/--
lemma `isQuotientMap_mk` / 引理 `isQuotientMap_mk`

English:
lemma isQuotientMap_mk
  statement: IsQuotientMap (ZerothHomotopy.mk (X := X))
  proof: isQuotientMap_quotient_mk'

中文:
引理 isQuotientMap_mk
  结论: 是商映射 (ZerothHomotopy.mk (X := X))
  证明: isQuotientMap_quotient_mk'
-/
lemma isQuotientMap_mk : IsQuotientMap (ZerothHomotopy.mk (X := X)) :=
  isQuotientMap_quotient_mk'

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (ZerothHomotopy Real)
  body: ⟨@Quotient.mk' Real (pathSetoid Real) 0⟩

中文:
实例 inhabited
  签名: : 可居 (ZerothHomotopy 实数)
  定义体: ⟨@Quotient.mk' Real (pathSetoid Real) 0⟩

Depends on / 依赖: Quotient, Quotient.mk, pathSetoid
-/
instance inhabited : Inhabited (ZerothHomotopy Real) :=
  ⟨@Quotient.mk' Real (pathSetoid Real) 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: X] : Nonempty (ZerothHomotopy X)
  body: ⟨.mk (Classical.arbitrary _)⟩

中文:
实例 [非空
  签名: X] : 非空 (ZerothHomotopy X)
  定义体: ⟨.mk (Classical.arbitrary _)⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
instance [Nonempty X] : Nonempty (ZerothHomotopy X) := ⟨.mk (Classical.arbitrary _)⟩

section

variable {T : Type*} (f : X -> T) (hf : forall ⦃x y : X⦄ (_ : Path x y), f x = f y)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : ZerothHomotopy X -> T
  body: Quotient.lift f fun _ _ ⟨p⟩ => hf p

@[simp]

中文:
定义 lift
  签名: : ZerothHomotopy X -> T
  定义体: Quotient.lift f fun _ _ ⟨p⟩ => hf p

@[simp]

Depends on / 依赖: Quotient, Quotient.lift
-/
def lift : ZerothHomotopy X -> T :=
  Quotient.lift f fun _ _ ⟨p⟩ => hf p

@[simp]
/--
lemma `lift_mk` / 引理 `lift_mk`

English:
lemma lift_mk
  given: (x : X)
  statement: lift f hf (.mk x) = f x
  proof: rfl

中文:
引理 lift_mk
  条件: (x : X)
  结论: lift f hf (.mk x) = f x
  证明: rfl
-/
lemma lift_mk (x : X) : lift f hf (.mk x) = f x := rfl

end

end ZerothHomotopy

variable {X}

/-! ### Being joined by a path inside a set -/


/--
Definition of `JoinedIn` / `JoinedIn` 的定义

English:
definition JoinedIn
  signature: (F : Set X) (x y : X)
  body: exists γ : Path x y, forall t, γ t in F

中文:
定义 JoinedIn
  签名: (F : 集合 X) (x y : X)
  定义体: exists γ : Path x y, forall t, γ t in F
-/
def JoinedIn (F : Set X) (x y : X) : Prop :=
  exists γ : Path x y, forall t, γ t in F

variable {F : Set X}

/--
theorem `JoinedIn.mem` / 定理 `JoinedIn.mem`

English:
theorem JoinedIn.mem
  given: (h : JoinedIn F x y)
  statement: x in F ∧ y in F
  proof: by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 in F ∧ γ 1 in F := by constructor <;> apply γ_in
  simpa using this

中文:
定理 JoinedIn.mem
  条件: (h : JoinedIn F x y)
  结论: x in F ∧ y in F
  证明: by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 in F ∧ γ 1 in F := by constructor <;> apply γ_in
  simpa using this
-/
theorem JoinedIn.mem (h : JoinedIn F x y) : x in F ∧ y in F := by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 in F ∧ γ 1 in F := by constructor <;> apply γ_in
  simpa using this

/--
theorem `JoinedIn.source_mem` / 定理 `JoinedIn.source_mem`

English:
theorem JoinedIn.source_mem
  given: (h : JoinedIn F x y)
  statement: x in F
  proof: h.mem.1

中文:
定理 JoinedIn.source_mem
  条件: (h : JoinedIn F x y)
  结论: x in F
  证明: h.mem.1

Depends on / 依赖: h.mem
-/
theorem JoinedIn.source_mem (h : JoinedIn F x y) : x in F :=
  h.mem.1

/--
theorem `JoinedIn.target_mem` / 定理 `JoinedIn.target_mem`

English:
theorem JoinedIn.target_mem
  given: (h : JoinedIn F x y)
  statement: y in F
  proof: h.mem.2

中文:
定理 JoinedIn.target_mem
  条件: (h : JoinedIn F x y)
  结论: y in F
  证明: h.mem.2

Depends on / 依赖: h.mem
-/
theorem JoinedIn.target_mem (h : JoinedIn F x y) : y in F :=
  h.mem.2

/--
Definition of `JoinedIn.somePath` / `JoinedIn.somePath` 的定义

English:
definition JoinedIn.somePath
  signature: (h : JoinedIn F x y)
  body: Classical.choose h

@[simp]

中文:
定义 JoinedIn.somePath
  签名: (h : JoinedIn F x y)
  定义体: Classical.choose h

@[simp]

Depends on / 依赖: Classical, Classical.choose
-/
def JoinedIn.somePath (h : JoinedIn F x y) : Path x y :=
  Classical.choose h

@[simp]
/--
theorem `JoinedIn.somePath_mem` / 定理 `JoinedIn.somePath_mem`

English:
theorem JoinedIn.somePath_mem
  given: (h : JoinedIn F x y) (t : I)
  statement: h.somePath t in F
  proof: Classical.choose_spec h t

中文:
定理 JoinedIn.somePath_mem
  条件: (h : JoinedIn F x y) (t : I)
  结论: h.somePath t in F
  证明: Classical.choose_spec h t

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
theorem JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I) : h.somePath t in F :=
  Classical.choose_spec h t

/--
theorem `JoinedIn.joined_subtype` / 定理 `JoinedIn.joined_subtype`

English:
theorem JoinedIn.joined_subtype
  given: (h : JoinedIn F x y)
  proof: ⟨{ toFun := fun t => ⟨h.somePath t, h.somePath_mem t⟩
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }⟩

中文:
定理 JoinedIn.joined_subtype
  条件: (h : JoinedIn F x y)
  证明: ⟨{ toFun := fun t => ⟨h.somePath t, h.somePath_mem t⟩
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }⟩

Depends on / 依赖: continuous_toFun, fun_prop, h.somePath, h.somePath_mem, somePath, somePath_mem, source, target
-/
theorem JoinedIn.joined_subtype (h : JoinedIn F x y) :
    Joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F) :=
  ⟨{ toFun := fun t => ⟨h.somePath t, h.somePath_mem t⟩
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }⟩

/--
theorem `JoinedIn.ofLine` / 定理 `JoinedIn.ofLine`

English:
theorem JoinedIn.ofLine
  statement: {f : Real -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
  proof: ⟨Path.ofLine hf h₀ h₁, fun t => hF Path.ofLine_mem hf h₀ h₁ t⟩

中文:
定理 JoinedIn.ofLine
  结论: {f : 实数 -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
  证明: ⟨Path.ofLine hf h₀ h₁, fun t => hF Path.ofLine_mem hf h₀ h₁ t⟩

Depends on / 依赖: Path.ofLine, Path.ofLine_mem, ofLine, ofLine_mem
-/
theorem JoinedIn.ofLine {f : Real -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
    (hF : f '' I subseteq F) : JoinedIn F x y :=
⟨Path.ofLine hf h₀ h₁, fun t => hF Path.ofLine_mem hf h₀ h₁ t⟩

/--
theorem `JoinedIn.joined` / 定理 `JoinedIn.joined`

English:
theorem JoinedIn.joined
  given: (h : JoinedIn F x y)
  statement: Joined x y
  proof: ⟨h.somePath⟩

中文:
定理 JoinedIn.joined
  条件: (h : JoinedIn F x y)
  结论: Joined x y
  证明: ⟨h.somePath⟩

Depends on / 依赖: h.somePath, somePath
-/
theorem JoinedIn.joined (h : JoinedIn F x y) : Joined x y :=
  ⟨h.somePath⟩

/--
theorem `joinedIn_iff_joined` / 定理 `joinedIn_iff_joined`

English:
theorem joinedIn_iff_joined
  given: (x_in : x in F) (y_in : y in F)
  proof: ⟨fun h => h.joined_subtype, fun h => ⟨h.somePath.map continuous_subtype_val, by simp⟩⟩

@[simp]

中文:
定理 joinedIn_iff_joined
  条件: (x_in : x in F) (y_in : y in F)
  证明: ⟨fun h => h.joined_subtype, fun h => ⟨h.somePath.map continuous_subtype_val, by simp⟩⟩

@[simp]

Depends on / 依赖: continuous_subtype_val, h.joined_subtype, h.somePath.map, joined_subtype, somePath
-/
theorem joinedIn_iff_joined (x_in : x in F) (y_in : y in F) :
    JoinedIn F x y ↔ Joined (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F) :=
  ⟨fun h => h.joined_subtype, fun h => ⟨h.somePath.map continuous_subtype_val, by simp⟩⟩

@[simp]
/--
theorem `joinedIn_univ` / 定理 `joinedIn_univ`

English:
theorem joinedIn_univ
  statement: JoinedIn univ x y ↔ Joined x y
  proof: by
  simp [JoinedIn, Joined, exists_true_iff_nonempty]

中文:
定理 joinedIn_univ
  结论: JoinedIn univ x y ↔ Joined x y
  证明: by
  simp [JoinedIn, Joined, exists_true_iff_nonempty]

Depends on / 依赖: Joined, JoinedIn, exists_true_iff_nonempty
-/
theorem joinedIn_univ : JoinedIn univ x y ↔ Joined x y := by
  simp [JoinedIn, Joined, exists_true_iff_nonempty]

/--
theorem `JoinedIn.mono` / 定理 `JoinedIn.mono`

English:
theorem JoinedIn.mono
  given: {U V : Set X} (h : JoinedIn U x y) (hUV : U subseteq V)
  statement: JoinedIn V x y
  proof: ⟨h.somePath, fun t => hUV (h.somePath_mem t)⟩

中文:
定理 JoinedIn.mono
  条件: {U V : 集合 X} (h : JoinedIn U x y) (hUV : U subseteq V)
  结论: JoinedIn V x y
  证明: ⟨h.somePath, fun t => hUV (h.somePath_mem t)⟩

Depends on / 依赖: h.somePath, h.somePath_mem, somePath, somePath_mem
-/
theorem JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U subseteq V) : JoinedIn V x y :=
  ⟨h.somePath, fun t => hUV (h.somePath_mem t)⟩

/--
theorem `JoinedIn.refl` / 定理 `JoinedIn.refl`

English:
theorem JoinedIn.refl
  given: (h : x in F)
  statement: JoinedIn F x x
  proof: ⟨Path.refl x, fun _t => h⟩

@[symm]

中文:
定理 JoinedIn.refl
  条件: (h : x in F)
  结论: JoinedIn F x x
  证明: ⟨Path.refl x, fun _t => h⟩

@[symm]

Depends on / 依赖: Path.refl
-/
theorem JoinedIn.refl (h : x in F) : JoinedIn F x x :=
  ⟨Path.refl x, fun _t => h⟩

@[symm]
/--
theorem `JoinedIn.symm` / 定理 `JoinedIn.symm`

English:
theorem JoinedIn.symm
  given: (h : JoinedIn F x y)
  statement: JoinedIn F y x
  proof: by
  obtain ⟨hx, hy⟩ := h.mem
  simp_all only [joinedIn_iff_joined]
  exact h.symm

中文:
定理 JoinedIn.symm
  条件: (h : JoinedIn F x y)
  结论: JoinedIn F y x
  证明: by
  obtain ⟨hx, hy⟩ := h.mem
  simp_all only [joinedIn_iff_joined]
  exact h.symm

Depends on / 依赖: h.mem, h.symm, joinedIn_iff_joined
-/
theorem JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x := by
  obtain ⟨hx, hy⟩ := h.mem
  simp_all only [joinedIn_iff_joined]
  exact h.symm

/--
theorem `JoinedIn.trans` / 定理 `JoinedIn.trans`

English:
theorem JoinedIn.trans
  given: (hxy : JoinedIn F x y) (hyz : JoinedIn F y z)
  statement: JoinedIn F x z
  proof: by
  obtain ⟨hx, hy⟩ := hxy.mem
  obtain ⟨hx, hy⟩ := hyz.mem
  simp_all only [joinedIn_iff_joined]
  exact hxy.trans hyz

中文:
定理 JoinedIn.trans
  条件: (hxy : JoinedIn F x y) (hyz : JoinedIn F y z)
  结论: JoinedIn F x z
  证明: by
  obtain ⟨hx, hy⟩ := hxy.mem
  obtain ⟨hx, hy⟩ := hyz.mem
  simp_all only [joinedIn_iff_joined]
  exact hxy.trans hyz

Depends on / 依赖: hxy.mem, hxy.trans, hyz.mem, joinedIn_iff_joined
-/
theorem JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F x z := by
  obtain ⟨hx, hy⟩ := hxy.mem
  obtain ⟨hx, hy⟩ := hyz.mem
  simp_all only [joinedIn_iff_joined]
  exact hxy.trans hyz

/--
theorem `Specializes.joinedIn` / 定理 `Specializes.joinedIn`

English:
theorem Specializes.joinedIn
  given: (h : x ⤳ y) (hx : x in F) (hy : y in F)
  statement: JoinedIn F x y
  proof: by
  refine ⟨⟨⟨Set.piecewise {1} (const I y) (const I x), ?_⟩, by simp, by simp⟩, fun t => ?_⟩
  · exact isClosed_singleton.continuous_piecewise_of_specializes continuous_const continuous_const
      fun _ => h
  · simp only [Path.coe_mk_mk, piecewise]
    split_ifs <;> assumption

中文:
定理 Specializes.joinedIn
  条件: (h : x ⤳ y) (hx : x in F) (hy : y in F)
  结论: JoinedIn F x y
  证明: by
  refine ⟨⟨⟨Set.piecewise {1} (const I y) (const I x), ?_⟩, by simp, by simp⟩, fun t => ?_⟩
  · exact isClosed_singleton.continuous_piecewise_of_specializes continuous_const continuous_const
      fun _ => h
  · simp only [Path.coe_mk_mk, piecewise]
    split_ifs <;> assumption

Depends on / 依赖: Path.coe_mk_mk, Set.piecewise, coe_mk_mk, continuous_const, continuous_piecewise_of_specializes, isClosed_singleton, isClosed_singleton.continuous_piecewise_of_specializes, piecewise, split_ifs
-/
theorem Specializes.joinedIn (h : x ⤳ y) (hx : x in F) (hy : y in F) : JoinedIn F x y := by
  refine ⟨⟨⟨Set.piecewise {1} (const I y) (const I x), ?_⟩, by simp, by simp⟩, fun t => ?_⟩
  · exact isClosed_singleton.continuous_piecewise_of_specializes continuous_const continuous_const
      fun _ => h
  · simp only [Path.coe_mk_mk, piecewise]
    split_ifs <;> assumption

/--
theorem `Inseparable.joinedIn` / 定理 `Inseparable.joinedIn`

English:
theorem Inseparable.joinedIn
  given: (h : Inseparable x y) (hx : x in F) (hy : y in F)
  statement: JoinedIn F x y
  proof: h.specializes.joinedIn hx hy

中文:
定理 不可分.joinedIn
  条件: (h : 不可分 x y) (hx : x in F) (hy : y in F)
  结论: JoinedIn F x y
  证明: h.specializes.joinedIn hx hy

Depends on / 依赖: h.specializes.joinedIn, joinedIn, specializes
-/
theorem Inseparable.joinedIn (h : Inseparable x y) (hx : x in F) (hy : y in F) : JoinedIn F x y :=
  h.specializes.joinedIn hx hy

/--
theorem `JoinedIn.map_continuousOn` / 定理 `JoinedIn.map_continuousOn`

English:
theorem JoinedIn.map_continuousOn
  given: (h : JoinedIn F x y) {f : X -> Y} (hf : ContinuousOn f F)
  proof: let ⟨γ, hγ⟩ := h
⟨γ.map' hf.mono (range_subset_iff.mpr hγ), fun t => mem_image_of_mem _ (hγ t)⟩

中文:
定理 JoinedIn.map_continuousOn
  条件: (h : JoinedIn F x y) {f : X -> Y} (hf : ContinuousOn f F)
  证明: let ⟨γ, hγ⟩ := h
⟨γ.map' hf.mono (range_subset_iff.mpr hγ), fun t => mem_image_of_mem _ (hγ t)⟩

Depends on / 依赖: hf.mono, mem_image_of_mem, range_subset_iff, range_subset_iff.mpr
-/
theorem JoinedIn.map_continuousOn (h : JoinedIn F x y) {f : X -> Y} (hf : ContinuousOn f F) :
    JoinedIn (f '' F) (f x) (f y) :=
  let ⟨γ, hγ⟩ := h
⟨γ.map' hf.mono (range_subset_iff.mpr hγ), fun t => mem_image_of_mem _ (hγ t)⟩

/--
theorem `JoinedIn.map` / 定理 `JoinedIn.map`

English:
theorem JoinedIn.map
  given: (h : JoinedIn F x y) {f : X -> Y} (hf : Continuous f)
  proof: h.map_continuousOn hf.continuousOn

中文:
定理 JoinedIn.map
  条件: (h : JoinedIn F x y) {f : X -> Y} (hf : 连续 f)
  证明: h.map_continuousOn hf.continuousOn

Depends on / 依赖: continuousOn, h.map_continuousOn, hf.continuousOn, map_continuousOn
-/
theorem JoinedIn.map (h : JoinedIn F x y) {f : X -> Y} (hf : Continuous f) :
    JoinedIn (f '' F) (f x) (f y) :=
  h.map_continuousOn hf.continuousOn

/--
theorem `Topology.IsInducing.joinedIn_image` / 定理 `Topology.IsInducing.joinedIn_image`

English:
theorem Topology.IsInducing.joinedIn_image
  statement: {f : X -> Y} (hf : IsInducing f) (hx : x in F)
  proof: by
  refine ⟨?_, (.map · hf.continuous)⟩
  rintro ⟨γ, hγ⟩
  choose γ' hγ'F hγ' using hγ
  have h₀ : x ⤳ γ' 0 := by rw [← hf.specializes_iff, hγ', γ.source]
  have h₁ : γ' 1 ⤳ y := by rw [← hf.specializes_iff, hγ', γ.target]
  have h : JoinedIn F (γ' 0) (γ' 1) := by
    refine ⟨⟨⟨γ', ?_⟩, rfl, rfl⟩, hγ'F⟩
    simpa only [hf.continuous_iff, comp_def, hγ'] using map_continuous γ
exact (h₀.joinedIn hx (hγ'F _)).trans h.trans h₁.joinedIn (hγ'F _) hy

@[to_additive]

中文:
定理 拓扑.是Inducing.joinedIn_image
  结论: {f : X -> Y} (hf : 是Inducing f) (hx : x in F)
  证明: by
  refine ⟨?_, (.map · hf.continuous)⟩
  rintro ⟨γ, hγ⟩
  choose γ' hγ'F hγ' using hγ
  have h₀ : x ⤳ γ' 0 := by rw [← hf.specializes_iff, hγ', γ.source]
  have h₁ : γ' 1 ⤳ y := by rw [← hf.specializes_iff, hγ', γ.target]
  have h : JoinedIn F (γ' 0) (γ' 1) := by
    refine ⟨⟨⟨γ', ?_⟩, rfl, rfl⟩, hγ'F⟩
    simpa only [hf.continuous_iff, comp_def, hγ'] using map_continuous γ
exact (h₀.joinedIn hx (hγ'F _)).trans h.trans h₁.joinedIn (hγ'F _) hy

@[to_additive]

Depends on / 依赖: JoinedIn, comp_def, continuous, continuous_iff, h.trans, hf.continuous, hf.continuous_iff, hf.specializes_iff, joinedIn, map_continuous, source, specializes_iff, target
-/
theorem Topology.IsInducing.joinedIn_image {f : X -> Y} (hf : IsInducing f) (hx : x in F)
    (hy : y in F) : JoinedIn (f '' F) (f x) (f y) ↔ JoinedIn F x y := by
  refine ⟨?_, (.map · hf.continuous)⟩
  rintro ⟨γ, hγ⟩
  choose γ' hγ'F hγ' using hγ
  have h₀ : x ⤳ γ' 0 := by rw [← hf.specializes_iff, hγ', γ.source]
  have h₁ : γ' 1 ⤳ y := by rw [← hf.specializes_iff, hγ', γ.target]
  have h : JoinedIn F (γ' 0) (γ' 1) := by
    refine ⟨⟨⟨γ', ?_⟩, rfl, rfl⟩, hγ'F⟩
    simpa only [hf.continuous_iff, comp_def, hγ'] using map_continuous γ
exact (h₀.joinedIn hx (hγ'F _)).trans h.trans h₁.joinedIn (hγ'F _) hy

@[to_additive]
/--
theorem `JoinedIn.mul` / 定理 `JoinedIn.mul`

English:
theorem JoinedIn.mul
  statement: {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
  proof: ⟨hs.somePath.mul ht.somePath, fun t => Set.mul_mem_mul (hs.somePath_mem t) (ht.somePath_mem t)⟩

@[to_additive]

中文:
定理 JoinedIn.mul
  结论: {M : 类型} [乘法 M] [拓扑空间 M] [连续乘法 M]
  证明: ⟨hs.somePath.mul ht.somePath, fun t => Set.mul_mem_mul (hs.somePath_mem t) (ht.somePath_mem t)⟩

@[to_additive]

Depends on / 依赖: Set.mul_mem_mul, hs.somePath.mul, hs.somePath_mem, ht.somePath, ht.somePath_mem, mul_mem_mul, somePath, somePath_mem
-/
theorem JoinedIn.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
    {s t : Set M} {a b c d : M} (hs : JoinedIn s a b) (ht : JoinedIn t c d) :
    JoinedIn (s * t) (a * c) (b * d) :=
  ⟨hs.somePath.mul ht.somePath, fun t => Set.mul_mem_mul (hs.somePath_mem t) (ht.somePath_mem t)⟩

@[to_additive]
/--
theorem `JoinedIn.inv` / 定理 `JoinedIn.inv`

English:
theorem JoinedIn.inv
  statement: {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [ContinuousInv G]
  proof: ⟨hs.somePath.inv, fun t => Set.inv_mem_inv.mpr (hs.somePath_mem t)⟩

中文:
定理 JoinedIn.inv
  结论: {G : 类型} [InvolutiveInv G] [拓扑空间 G] [连续取逆 G]
  证明: ⟨hs.somePath.inv, fun t => Set.inv_mem_inv.mpr (hs.somePath_mem t)⟩

Depends on / 依赖: Set.inv_mem_inv.mpr, hs.somePath.inv, hs.somePath_mem, inv_mem_inv, somePath, somePath_mem
-/
theorem JoinedIn.inv {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [ContinuousInv G]
    {s : Set G} {a b : G} (hs : JoinedIn s a b) :
    JoinedIn s⁻¹ a⁻¹ b⁻¹ :=
  ⟨hs.somePath.inv, fun t => Set.inv_mem_inv.mpr (hs.somePath_mem t)⟩

/-! ### Path component -/

/--
Definition of `pathComponent` / `pathComponent` 的定义

English:
definition pathComponent
  signature: (x : X)
  body: { y | Joined x y }

中文:
定义 pathComponent
  签名: (x : X)
  定义体: { y | Joined x y }

Depends on / 依赖: Joined
-/
def pathComponent (x : X) :=
  { y | Joined x y }

/--
theorem `mem_pathComponent_iff` / 定理 `mem_pathComponent_iff`

English:
theorem mem_pathComponent_iff
  statement: x in pathComponent y ↔ Joined y x
  proof: .rfl

@[simp]

中文:
定理 mem_pathComponent_iff
  结论: x in pathComponent y ↔ Joined y x
  证明: .rfl

@[simp]
-/
theorem mem_pathComponent_iff : x in pathComponent y ↔ Joined y x := .rfl

@[simp]
/--
theorem `mem_pathComponent_self` / 定理 `mem_pathComponent_self`

English:
theorem mem_pathComponent_self
  given: (x : X)
  statement: x in pathComponent x
  proof: Joined.refl x

@[simp]

中文:
定理 mem_pathComponent_self
  条件: (x : X)
  结论: x in pathComponent x
  证明: Joined.refl x

@[simp]

Depends on / 依赖: Joined, Joined.refl
-/
theorem mem_pathComponent_self (x : X) : x in pathComponent x :=
  Joined.refl x

@[simp]
/--
theorem `pathComponent.nonempty` / 定理 `pathComponent.nonempty`

English:
theorem pathComponent.nonempty
  given: (x : X)
  statement: (pathComponent x).Nonempty
  proof: ⟨x, mem_pathComponent_self x⟩

中文:
定理 pathComponent.nonempty
  条件: (x : X)
  结论: (pathComponent x).非空
  证明: ⟨x, mem_pathComponent_self x⟩

Depends on / 依赖: mem_pathComponent_self
-/
theorem pathComponent.nonempty (x : X) : (pathComponent x).Nonempty :=
  ⟨x, mem_pathComponent_self x⟩

/--
theorem `mem_pathComponent_of_mem` / 定理 `mem_pathComponent_of_mem`

English:
theorem mem_pathComponent_of_mem
  given: (h : x in pathComponent y)
  statement: y in pathComponent x
  proof: Joined.symm h

中文:
定理 mem_pathComponent_of_mem
  条件: (h : x in pathComponent y)
  结论: y in pathComponent x
  证明: Joined.symm h

Depends on / 依赖: Joined, Joined.symm
-/
theorem mem_pathComponent_of_mem (h : x in pathComponent y) : y in pathComponent x :=
  Joined.symm h

/--
theorem `pathComponent_symm` / 定理 `pathComponent_symm`

English:
theorem pathComponent_symm
  statement: x in pathComponent y ↔ y in pathComponent x
  proof: ⟨fun h => mem_pathComponent_of_mem h, fun h => mem_pathComponent_of_mem h⟩

中文:
定理 pathComponent_symm
  结论: x in pathComponent y ↔ y in pathComponent x
  证明: ⟨fun h => mem_pathComponent_of_mem h, fun h => mem_pathComponent_of_mem h⟩

Depends on / 依赖: mem_pathComponent_of_mem
-/
theorem pathComponent_symm : x in pathComponent y ↔ y in pathComponent x :=
  ⟨fun h => mem_pathComponent_of_mem h, fun h => mem_pathComponent_of_mem h⟩

/--
theorem `pathComponent_congr` / 定理 `pathComponent_congr`

English:
theorem pathComponent_congr
  given: (h : x in pathComponent y)
  statement: pathComponent x = pathComponent y
  proof: by
  ext z
  constructor
  · intro h'
    rw [pathComponent_symm]
    exact (h.trans h').symm
  · intro h'
    rw [pathComponent_symm] at h' ⊢
    exact h'.trans h

中文:
定理 pathComponent_congr
  条件: (h : x in pathComponent y)
  结论: pathComponent x = pathComponent y
  证明: by
  ext z
  constructor
  · intro h'
    rw [pathComponent_symm]
    exact (h.trans h').symm
  · intro h'
    rw [pathComponent_symm] at h' ⊢
    exact h'.trans h

Depends on / 依赖: h.trans, pathComponent_symm
-/
theorem pathComponent_congr (h : x in pathComponent y) : pathComponent x = pathComponent y := by
  ext z
  constructor
  · intro h'
    rw [pathComponent_symm]
    exact (h.trans h').symm
  · intro h'
    rw [pathComponent_symm] at h' ⊢
    exact h'.trans h

/--
theorem `pathComponent_subset_component` / 定理 `pathComponent_subset_component`

English:
theorem pathComponent_subset_component
  given: (x : X)
  statement: pathComponent x subseteq connectedComponent x
  proof: fun y h =>
  (isConnected_range h.somePath.continuous).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩

中文:
定理 pathComponent_subset_component
  条件: (x : X)
  结论: pathComponent x subseteq connectedComponent x
  证明: fun y h =>
  (isConnected_range h.somePath.continuous).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩

Depends on / 依赖: continuous, h.somePath.continuous, isConnected_range, somePath, subset_connectedComponent
-/
theorem pathComponent_subset_component (x : X) : pathComponent x subseteq connectedComponent x :=
  fun y h =>
  (isConnected_range h.somePath.continuous).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩

/--
theorem `biUnion_connectedComponent_pathComponent_eq` / 定理 `biUnion_connectedComponent_pathComponent_eq`

English:
theorem biUnion_connectedComponent_pathComponent_eq
  given: (x : X)
  proof: by
  simp only [Set.ext_iff, mem_iUnion₂]
  exact fun z => ⟨fun ⟨y, hy, hz⟩ => connectedComponent_eq hy ▸ pathComponent_subset_component _ hz,
    (⟨z, ·, mem_pathComponent_self z⟩)⟩

中文:
定理 biUnion_connectedComponent_pathComponent_eq
  条件: (x : X)
  证明: by
  simp only [Set.ext_iff, mem_iUnion₂]
  exact fun z => ⟨fun ⟨y, hy, hz⟩ => connectedComponent_eq hy ▸ pathComponent_subset_component _ hz,
    (⟨z, ·, mem_pathComponent_self z⟩)⟩

Depends on / 依赖: Set.ext_iff, connectedComponent_eq, ext_iff, mem_pathComponent_self, pathComponent_subset_component
-/
theorem biUnion_connectedComponent_pathComponent_eq (x : X) :
    (⋃ y in connectedComponent x, pathComponent y) = connectedComponent x := by
  simp only [Set.ext_iff, mem_iUnion₂]
  exact fun z => ⟨fun ⟨y, hy, hz⟩ => connectedComponent_eq hy ▸ pathComponent_subset_component _ hz,
    (⟨z, ·, mem_pathComponent_self z⟩)⟩

/--
Definition of `ZerothHomotopy.toConnectedComponents` / `ZerothHomotopy.toConnectedComponents` 的定义

English:
definition ZerothHomotopy.toConnectedComponents
  signature: : ZerothHomotopy X -> ConnectedComponents X
  body: Quotient.map id fun x _ h => connectedComponent_eq pathComponent_subset_component x h

@[simp]

中文:
定义 ZerothHomotopy.toConnectedComponents
  签名: : ZerothHomotopy X -> ConnectedComponents X
  定义体: Quotient.map id fun x _ h => connectedComponent_eq pathComponent_subset_component x h

@[simp]

Depends on / 依赖: Quotient, Quotient.map, connectedComponent_eq, pathComponent_subset_component
-/
def ZerothHomotopy.toConnectedComponents : ZerothHomotopy X -> ConnectedComponents X :=
Quotient.map id fun x _ h => connectedComponent_eq pathComponent_subset_component x h

@[simp]
/--
theorem `ZerothHomotopy.toConnectedComponents_apply` / 定理 `ZerothHomotopy.toConnectedComponents_apply`

English:
theorem ZerothHomotopy.toConnectedComponents_apply
  given: (x : X)
  proof: rfl

中文:
定理 ZerothHomotopy.toConnectedComponents_apply
  条件: (x : X)
  证明: rfl
-/
theorem ZerothHomotopy.toConnectedComponents_apply (x : X) :
    toConnectedComponents (.mk x) = ⟦x⟧ := rfl

/--
theorem `ZerothHomotopy.toConnectedComponents_surjective` / 定理 `ZerothHomotopy.toConnectedComponents_surjective`

English:
theorem ZerothHomotopy.toConnectedComponents_surjective
  proof: toConnectedComponents (X := X)
  Quotient.map_surjective _ surjective_id

中文:
定理 ZerothHomotopy.toConnectedComponents_surjective
  证明: toConnectedComponents (X := X)
  Quotient.map_surjective _ surjective_id

Depends on / 依赖: toConnectedComponents
-/
theorem ZerothHomotopy.toConnectedComponents_surjective :
.Surjective := toConnectedComponents (X := X)
  Quotient.map_surjective _ surjective_id

/--
Definition of `pathComponentIn` / `pathComponentIn` 的定义

English:
definition pathComponentIn
  signature: (F : Set X) (x : X)
  body: { y | JoinedIn F x y }

@[simp]

中文:
定义 pathComponentIn
  签名: (F : 集合 X) (x : X)
  定义体: { y | JoinedIn F x y }

@[simp]

Depends on / 依赖: JoinedIn
-/
def pathComponentIn (F : Set X) (x : X) :=
  { y | JoinedIn F x y }

@[simp]
/--
theorem `pathComponentIn_univ` / 定理 `pathComponentIn_univ`

English:
theorem pathComponentIn_univ
  given: (x : X)
  statement: pathComponentIn univ x = pathComponent x
  proof: by
  simp [pathComponentIn, pathComponent, JoinedIn, Joined, exists_true_iff_nonempty]

中文:
定理 pathComponentIn_univ
  条件: (x : X)
  结论: pathComponentIn univ x = pathComponent x
  证明: by
  simp [pathComponentIn, pathComponent, JoinedIn, Joined, exists_true_iff_nonempty]

Depends on / 依赖: Joined, JoinedIn, exists_true_iff_nonempty, pathComponent, pathComponentIn
-/
theorem pathComponentIn_univ (x : X) : pathComponentIn univ x = pathComponent x := by
  simp [pathComponentIn, pathComponent, JoinedIn, Joined, exists_true_iff_nonempty]

/--
theorem `Joined.mem_pathComponent` / 定理 `Joined.mem_pathComponent`

English:
theorem Joined.mem_pathComponent
  given: (hyz : Joined y z) (hxy : y in pathComponent x)
  proof: hxy.trans hyz

中文:
定理 Joined.mem_pathComponent
  条件: (hyz : Joined y z) (hxy : y in pathComponent x)
  证明: hxy.trans hyz

Depends on / 依赖: hxy.trans
-/
theorem Joined.mem_pathComponent (hyz : Joined y z) (hxy : y in pathComponent x) :
    z in pathComponent x :=
  hxy.trans hyz

/--
theorem `mem_pathComponentIn_self` / 定理 `mem_pathComponentIn_self`

English:
theorem mem_pathComponentIn_self
  given: (h : x in F)
  statement: x in pathComponentIn F x
  proof: JoinedIn.refl h

中文:
定理 mem_pathComponentIn_self
  条件: (h : x in F)
  结论: x in pathComponentIn F x
  证明: JoinedIn.refl h

Depends on / 依赖: JoinedIn, JoinedIn.refl
-/
theorem mem_pathComponentIn_self (h : x in F) : x in pathComponentIn F x :=
  JoinedIn.refl h

/--
theorem `pathComponentIn_subset` / 定理 `pathComponentIn_subset`

English:
theorem pathComponentIn_subset
  statement: pathComponentIn F x subseteq F
  proof: fun _ hy => hy.target_mem

中文:
定理 pathComponentIn_subset
  结论: pathComponentIn F x subseteq F
  证明: fun _ hy => hy.target_mem

Depends on / 依赖: hy.target_mem, target_mem
-/
theorem pathComponentIn_subset : pathComponentIn F x subseteq F :=
  fun _ hy => hy.target_mem

/--
theorem `pathComponentIn_nonempty_iff` / 定理 `pathComponentIn_nonempty_iff`

English:
theorem pathComponentIn_nonempty_iff
  statement: (pathComponentIn F x).Nonempty ↔ x in F
  proof: ⟨fun ⟨_, ⟨γ, hγ⟩⟩ => γ.source ▸ hγ 0, fun hx => ⟨x, mem_pathComponentIn_self hx⟩⟩

中文:
定理 pathComponentIn_nonempty_iff
  结论: (pathComponentIn F x).非空 ↔ x in F
  证明: ⟨fun ⟨_, ⟨γ, hγ⟩⟩ => γ.source ▸ hγ 0, fun hx => ⟨x, mem_pathComponentIn_self hx⟩⟩

Depends on / 依赖: mem_pathComponentIn_self, source
-/
theorem pathComponentIn_nonempty_iff : (pathComponentIn F x).Nonempty ↔ x in F :=
  ⟨fun ⟨_, ⟨γ, hγ⟩⟩ => γ.source ▸ hγ 0, fun hx => ⟨x, mem_pathComponentIn_self hx⟩⟩

/--
theorem `pathComponentIn_congr` / 定理 `pathComponentIn_congr`

English:
theorem pathComponentIn_congr
  given: (h : x in pathComponentIn F y)
  proof: by
  ext; exact ⟨h.trans, h.symm.trans⟩

@[gcongr]

中文:
定理 pathComponentIn_congr
  条件: (h : x in pathComponentIn F y)
  证明: by
  ext; exact ⟨h.trans, h.symm.trans⟩

@[gcongr]

Depends on / 依赖: h.symm.trans, h.trans
-/
theorem pathComponentIn_congr (h : x in pathComponentIn F y) :
    pathComponentIn F x = pathComponentIn F y := by
  ext; exact ⟨h.trans, h.symm.trans⟩

@[gcongr]
/--
theorem `pathComponentIn_mono` / 定理 `pathComponentIn_mono`

English:
theorem pathComponentIn_mono
  given: {G : Set X} (h : F subseteq G)
  proof: fun _ ⟨γ, hγ⟩ => ⟨γ, fun t => h (hγ t)⟩

中文:
定理 pathComponentIn_mono
  条件: {G : 集合 X} (h : F subseteq G)
  证明: fun _ ⟨γ, hγ⟩ => ⟨γ, fun t => h (hγ t)⟩
-/
theorem pathComponentIn_mono {G : Set X} (h : F subseteq G) :
    pathComponentIn F x subseteq pathComponentIn G x :=
  fun _ ⟨γ, hγ⟩ => ⟨γ, fun t => h (hγ t)⟩

/-! ### Path component of the identity in a group -/

/-- The path component of the identity in a topological monoid, as a submonoid. -/
@[to_additive (attr := simps) /-- The path component of the identity in an additive topological
monoid, as an additive submonoid. -/]
/--
Definition of `Submonoid.pathComponentOne` / `Submonoid.pathComponentOne` 的定义

English:
definition Submonoid.pathComponentOne
  signature: (M : Type*) [Monoid M] [TopologicalSpace M] [ContinuousMul M]
  body: pathComponent (1 : M)
  mul_mem' {m₁ m₂} hm₁ hm₂ := by simpa using! hm₁.mul hm₂
  one_mem' := mem_pathComponent_self 1

中文:
定义 子幺半群.pathComponentOne
  签名: (M : 类型) [幺半群 M] [拓扑空间 M] [连续乘法 M]
  定义体: pathComponent (1 : M)
  mul_mem' {m₁ m₂} hm₁ hm₂ := by simpa using! hm₁.mul hm₂
  one_mem' := mem_pathComponent_self 1

Depends on / 依赖: pathComponent
-/
def Submonoid.pathComponentOne (M : Type*) [Monoid M] [TopologicalSpace M] [ContinuousMul M] :
    Submonoid M where
  carrier := pathComponent (1 : M)
  mul_mem' {m₁ m₂} hm₁ hm₂ := by simpa using! hm₁.mul hm₂
  one_mem' := mem_pathComponent_self 1

/-- The path component of the identity in a topological group, as a subgroup. -/
@[to_additive (attr := simps!) /-- The path component of the identity in an additive topological
group, as an additive subgroup. -/]
/--
Definition of `Subgroup.pathComponentOne` / `Subgroup.pathComponentOne` 的定义

English:
definition Subgroup.pathComponentOne
  signature: (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  body: .pathComponentOne G
  inv_mem' {g} hg := by simpa using! hg.inv

中文:
定义 子群.pathComponentOne
  签名: (G : 类型) [群 G] [拓扑空间 G] [是拓扑群 G]
  定义体: .pathComponentOne G
  inv_mem' {g} hg := by simpa using! hg.inv

Depends on / 依赖: pathComponentOne
-/
def Subgroup.pathComponentOne (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Subgroup G where
  toSubmonoid := .pathComponentOne G
  inv_mem' {g} hg := by simpa using! hg.inv

/-- The path component of the identity in a topological group is normal. -/
@[to_additive]
/--
Instance `Subgroup.Normal.pathComponentOne` / 实例 `Subgroup.Normal.pathComponentOne`

English:
instance Subgroup.Normal.pathComponentOne
  signature: (G : Type*) [Group G] [TopologicalSpace G]
  body: fun ⟨γ⟩ g => ⟨⟨⟨(g * γ · * g⁻¹), by fun_prop⟩, by simp, by simp⟩⟩

中文:
实例 子群.正规.pathComponentOne
  签名: (G : 类型) [群 G] [拓扑空间 G]
  定义体: fun ⟨γ⟩ g => ⟨⟨⟨(g * γ · * g⁻¹), by fun_prop⟩, by simp, by simp⟩⟩

Depends on / 依赖: fun_prop
-/
instance Subgroup.Normal.pathComponentOne (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (Subgroup.pathComponentOne G).Normal where
  conj_mem _ := fun ⟨γ⟩ g => ⟨⟨⟨(g * γ · * g⁻¹), by fun_prop⟩, by simp, by simp⟩⟩

/-! ### Path connected sets -/


/--
Definition of `IsPathConnected` / `IsPathConnected` 的定义

English:
definition IsPathConnected
  signature: (F : Set X)
  body: exists x in F, forall ⦃y⦄, y in F -> JoinedIn F x y

中文:
定义 是道路连通
  签名: (F : 集合 X)
  定义体: exists x in F, forall ⦃y⦄, y in F -> JoinedIn F x y

Depends on / 依赖: JoinedIn
-/
def IsPathConnected (F : Set X) : Prop :=
  exists x in F, forall ⦃y⦄, y in F -> JoinedIn F x y

/--
theorem `isPathConnected_iff_eq` / 定理 `isPathConnected_iff_eq`

English:
theorem isPathConnected_iff_eq
  statement: IsPathConnected F ↔ exists x in F, pathComponentIn F x = F
  proof: by
  constructor <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
  · ext y
    exact ⟨fun hy => hy.mem.2, @h _⟩
  · intro y y_in
    rwa [← h] at y_in

中文:
定理 isPathConnected_iff_eq
  结论: 是道路连通 F ↔ 存在 x in F, pathComponentIn F x = F
  证明: by
  constructor <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
  · ext y
    exact ⟨fun hy => hy.mem.2, @h _⟩
  · intro y y_in
    rwa [← h] at y_in

Depends on / 依赖: hy.mem, x_in, y_in
-/
theorem isPathConnected_iff_eq : IsPathConnected F ↔ exists x in F, pathComponentIn F x = F := by
  constructor <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
  · ext y
    exact ⟨fun hy => hy.mem.2, @h _⟩
  · intro y y_in
    rwa [← h] at y_in

/--
theorem `IsPathConnected.joinedIn` / 定理 `IsPathConnected.joinedIn`

English:
theorem IsPathConnected.joinedIn
  given: (h : IsPathConnected F)
  proof: fun _x x_in _y y_in =>
  let ⟨_b, _b_in, hb⟩ := h
  (hb x_in).symm.trans (hb y_in)

中文:
定理 是道路连通.joinedIn
  条件: (h : 是道路连通 F)
  证明: fun _x x_in _y y_in =>
  let ⟨_b, _b_in, hb⟩ := h
  (hb x_in).symm.trans (hb y_in)

Depends on / 依赖: x_in, y_in
-/
theorem IsPathConnected.joinedIn (h : IsPathConnected F) :
    forallᵉ (x in F) (y in F), JoinedIn F x y := fun _x x_in _y y_in =>
  let ⟨_b, _b_in, hb⟩ := h
  (hb x_in).symm.trans (hb y_in)

/--
theorem `isPathConnected_iff` / 定理 `isPathConnected_iff`

English:
theorem isPathConnected_iff
  proof: ⟨fun h =>
    ⟨let ⟨b, b_in, _hb⟩ := h; ⟨b, b_in⟩, h.joinedIn⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, h _ b_in⟩⟩

中文:
定理 isPathConnected_iff
  证明: ⟨fun h =>
    ⟨let ⟨b, b_in, _hb⟩ := h; ⟨b, b_in⟩, h.joinedIn⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, h _ b_in⟩⟩

Depends on / 依赖: b_in, h.joinedIn, joinedIn
-/
theorem isPathConnected_iff :
    IsPathConnected F ↔ F.Nonempty ∧ forallᵉ (x in F) (y in F), JoinedIn F x y :=
  ⟨fun h =>
    ⟨let ⟨b, b_in, _hb⟩ := h; ⟨b, b_in⟩, h.joinedIn⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, h _ b_in⟩⟩

/--
theorem `IsPathConnected.nonempty` / 定理 `IsPathConnected.nonempty`

English:
theorem IsPathConnected.nonempty
  given: (h : IsPathConnected F)
  statement: F.Nonempty
  proof: .1 isPathConnected_iff.mp h

中文:
定理 是道路连通.nonempty
  条件: (h : 是道路连通 F)
  结论: F.非空
  证明: .1 isPathConnected_iff.mp h

Depends on / 依赖: isPathConnected_iff, isPathConnected_iff.mp
-/
theorem IsPathConnected.nonempty (h : IsPathConnected F) : F.Nonempty :=
.1 isPathConnected_iff.mp h

/--
theorem `IsPathConnected.image'` / 定理 `IsPathConnected.image'`

English:
theorem IsPathConnected.image'
  statement: (hF : IsPathConnected F)
  proof: by
  rcases hF with ⟨x, x_in, hx⟩
  use f x, mem_image_of_mem f x_in
  rintro _ ⟨y, y_in, rfl⟩
  refine ⟨(hx y_in).somePath.map' ?_, fun t => ⟨_, (hx y_in).somePath_mem t, rfl⟩⟩
  exact hf.mono (range_subset_iff.2 (hx y_in).somePath_mem)

中文:
定理 是道路连通.像'
  结论: (hF : 是道路连通 F)
  证明: by
  rcases hF with ⟨x, x_in, hx⟩
  use f x, mem_image_of_mem f x_in
  rintro _ ⟨y, y_in, rfl⟩
  refine ⟨(hx y_in).somePath.map' ?_, fun t => ⟨_, (hx y_in).somePath_mem t, rfl⟩⟩
  exact hf.mono (range_subset_iff.2 (hx y_in).somePath_mem)

Depends on / 依赖: hf.mono, mem_image_of_mem, range_subset_iff, somePath, somePath.map, somePath_mem, x_in, y_in
-/
theorem IsPathConnected.image' (hF : IsPathConnected F)
    {f : X -> Y} (hf : ContinuousOn f F) : IsPathConnected (f '' F) := by
  rcases hF with ⟨x, x_in, hx⟩
  use f x, mem_image_of_mem f x_in
  rintro _ ⟨y, y_in, rfl⟩
  refine ⟨(hx y_in).somePath.map' ?_, fun t => ⟨_, (hx y_in).somePath_mem t, rfl⟩⟩
  exact hf.mono (range_subset_iff.2 (hx y_in).somePath_mem)

/--
theorem `IsPathConnected.image` / 定理 `IsPathConnected.image`

English:
theorem IsPathConnected.image
  given: (hF : IsPathConnected F) {f : X -> Y} (hf : Continuous f)
  proof: hF.image' hf.continuousOn

@[to_additive]

中文:
定理 是道路连通.像
  条件: (hF : 是道路连通 F) {f : X -> Y} (hf : 连续 f)
  证明: hF.image' hf.continuousOn

@[to_additive]

Depends on / 依赖: continuousOn, hF.image, hf.continuousOn
-/
theorem IsPathConnected.image (hF : IsPathConnected F) {f : X -> Y} (hf : Continuous f) :
    IsPathConnected (f '' F) :=
  hF.image' hf.continuousOn

@[to_additive]
/--
theorem `IsPathConnected.mul` / 定理 `IsPathConnected.mul`

English:
theorem IsPathConnected.mul
  statement: {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
  proof: let ⟨a, ha_mem, ha⟩ := hs; let ⟨b, hb_mem, hb⟩ := ht
  ⟨a * b, mul_mem_mul ha_mem hb_mem, Set.forall_mem_image2.2 fun _x hx _y hy => (ha hx).mul (hb hy)⟩

@[to_additive]

中文:
定理 是道路连通.mul
  结论: {M : 类型} [乘法 M] [拓扑空间 M] [连续乘法 M]
  证明: let ⟨a, ha_mem, ha⟩ := hs; let ⟨b, hb_mem, hb⟩ := ht
  ⟨a * b, mul_mem_mul ha_mem hb_mem, Set.forall_mem_image2.2 fun _x hx _y hy => (ha hx).mul (hb hy)⟩

@[to_additive]

Depends on / 依赖: Set.forall_mem_image2, forall_mem_image2, ha_mem, hb_mem, mul_mem_mul
-/
theorem IsPathConnected.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
    {s t : Set M} (hs : IsPathConnected s) (ht : IsPathConnected t) :
    IsPathConnected (s * t) :=
  let ⟨a, ha_mem, ha⟩ := hs; let ⟨b, hb_mem, hb⟩ := ht
  ⟨a * b, mul_mem_mul ha_mem hb_mem, Set.forall_mem_image2.2 fun _x hx _y hy => (ha hx).mul (hb hy)⟩

@[to_additive]
/--
theorem `IsPathConnected.inv` / 定理 `IsPathConnected.inv`

English:
theorem IsPathConnected.inv
  statement: {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [ContinuousInv G]
  proof: let ⟨a, ha_mem, ha⟩ := hs
.map continuous_inv⟩ ⟨a⁻¹, inv_mem_inv.mpr ha_mem, fun x hx => by simpa using ha (mem_inv.mp hx)

中文:
定理 是道路连通.inv
  结论: {G : 类型} [InvolutiveInv G] [拓扑空间 G] [连续取逆 G]
  证明: let ⟨a, ha_mem, ha⟩ := hs
.map continuous_inv⟩ ⟨a⁻¹, inv_mem_inv.mpr ha_mem, fun x hx => by simpa using ha (mem_inv.mp hx)

Depends on / 依赖: continuous_inv, ha_mem, inv_mem_inv, inv_mem_inv.mpr, mem_inv, mem_inv.mp
-/
theorem IsPathConnected.inv {G : Type*} [InvolutiveInv G] [TopologicalSpace G] [ContinuousInv G]
    {s : Set G} (hs : IsPathConnected s) :
    IsPathConnected s⁻¹ :=
  let ⟨a, ha_mem, ha⟩ := hs
.map continuous_inv⟩ ⟨a⁻¹, inv_mem_inv.mpr ha_mem, fun x hx => by simpa using ha (mem_inv.mp hx)

/-- If `f : X → Y` is an inducing map, `f(F)` is path-connected iff `F` is. -/
nonrec theorem Topology.IsInducing.isPathConnected_iff {f : X -> Y} (hf : IsInducing f) :
    IsPathConnected F ↔ IsPathConnected (f '' F) := by
  simp only [IsPathConnected, forall_mem_image, exists_mem_image]
  refine exists_congr fun x => and_congr_right fun hx => forall₂_congr fun y hy => ?_
  rw [hf.joinedIn_image hx hy]

/-- If `h : X → Y` is a homeomorphism, `h(s)` is path-connected iff `s` is. -/
@[simp]
/--
theorem `Homeomorph.isPathConnected_image` / 定理 `Homeomorph.isPathConnected_image`

English:
theorem Homeomorph.isPathConnected_image
  given: {s : Set X} (h : X ≃ₜ Y)
  proof: h.isInducing.isPathConnected_iff.symm

中文:
定理 同胚.isPathConnected_image
  条件: {s : 集合 X} (h : X ≃ₜ Y)
  证明: h.isInducing.isPathConnected_iff.symm

Depends on / 依赖: h.isInducing.isPathConnected_iff.symm, isInducing, isPathConnected_iff
-/
theorem Homeomorph.isPathConnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsPathConnected (h '' s) ↔ IsPathConnected s :=
  h.isInducing.isPathConnected_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is path-connected iff `s` is. -/
@[simp]
/--
theorem `Homeomorph.isPathConnected_preimage` / 定理 `Homeomorph.isPathConnected_preimage`

English:
theorem Homeomorph.isPathConnected_preimage
  given: {s : Set Y} (h : X ≃ₜ Y)
  proof: by
  rw [← Homeomorph.image_symm]; exact h.symm.isPathConnected_image

中文:
定理 同胚.isPathConnected_preimage
  条件: {s : 集合 Y} (h : X ≃ₜ Y)
  证明: by
  rw [← Homeomorph.image_symm]; exact h.symm.isPathConnected_image

Depends on / 依赖: Homeomorph, Homeomorph.image_symm, h.symm.isPathConnected_image, image_symm, isPathConnected_image
-/
theorem Homeomorph.isPathConnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsPathConnected (h ⁻¹' s) ↔ IsPathConnected s := by
  rw [← Homeomorph.image_symm]; exact h.symm.isPathConnected_image

/--
theorem `IsPathConnected.mem_pathComponent` / 定理 `IsPathConnected.mem_pathComponent`

English:
theorem IsPathConnected.mem_pathComponent
  given: (h : IsPathConnected F) (x_in : x in F) (y_in : y in F)
  proof: (h.joinedIn x x_in y y_in).joined

中文:
定理 是道路连通.mem_pathComponent
  条件: (h : 是道路连通 F) (x_in : x in F) (y_in : y in F)
  证明: (h.joinedIn x x_in y y_in).joined

Depends on / 依赖: h.joinedIn, joined, joinedIn, x_in, y_in
-/
theorem IsPathConnected.mem_pathComponent (h : IsPathConnected F) (x_in : x in F) (y_in : y in F) :
    y in pathComponent x :=
  (h.joinedIn x x_in y y_in).joined

/--
theorem `IsPathConnected.subset_pathComponent` / 定理 `IsPathConnected.subset_pathComponent`

English:
theorem IsPathConnected.subset_pathComponent
  given: (h : IsPathConnected F) (x_in : x in F)
  proof: fun _y y_in => h.mem_pathComponent x_in y_in

中文:
定理 是道路连通.subset_pathComponent
  条件: (h : 是道路连通 F) (x_in : x in F)
  证明: fun _y y_in => h.mem_pathComponent x_in y_in

Depends on / 依赖: h.mem_pathComponent, mem_pathComponent, x_in, y_in
-/
theorem IsPathConnected.subset_pathComponent (h : IsPathConnected F) (x_in : x in F) :
    F subseteq pathComponent x := fun _y y_in => h.mem_pathComponent x_in y_in

/--
theorem `IsPathConnected.subset_pathComponentIn` / 定理 `IsPathConnected.subset_pathComponentIn`

English:
theorem IsPathConnected.subset_pathComponentIn
  statement: {s : Set X} (hs : IsPathConnected s)
  proof: fun y hys => (hs.joinedIn x hxs y hys).mono hsF

中文:
定理 是道路连通.subset_pathComponentIn
  结论: {s : 集合 X} (hs : 是道路连通 s)
  证明: fun y hys => (hs.joinedIn x hxs y hys).mono hsF

Depends on / 依赖: hs.joinedIn, joinedIn
-/
theorem IsPathConnected.subset_pathComponentIn {s : Set X} (hs : IsPathConnected s)
    (hxs : x in s) (hsF : s subseteq F) : s subseteq pathComponentIn F x :=
  fun y hys => (hs.joinedIn x hxs y hys).mono hsF

/--
theorem `isPathConnected_singleton` / 定理 `isPathConnected_singleton`

English:
theorem isPathConnected_singleton
  given: (x : X)
  statement: IsPathConnected ({x} : Set X)
  proof: by
  refine ⟨x, rfl, ?_⟩
  rintro y rfl
  exact JoinedIn.refl rfl

中文:
定理 isPathConnected_singleton
  条件: (x : X)
  结论: 是道路连通 ({x} : 集合 X)
  证明: by
  refine ⟨x, rfl, ?_⟩
  rintro y rfl
  exact JoinedIn.refl rfl

Depends on / 依赖: JoinedIn, JoinedIn.refl
-/
theorem isPathConnected_singleton (x : X) : IsPathConnected ({x} : Set X) := by
  refine ⟨x, rfl, ?_⟩
  rintro y rfl
  exact JoinedIn.refl rfl

/--
theorem `isPathConnected_pathComponentIn` / 定理 `isPathConnected_pathComponentIn`

English:
theorem isPathConnected_pathComponentIn
  given: (h : x in F)
  statement: IsPathConnected (pathComponentIn F x)
  proof: ⟨x, mem_pathComponentIn_self h, fun _ ⟨γ, hγ⟩ => by
    refine ⟨γ, fun t =>
      ⟨(γ.truncateOfLE t.2.1).cast (γ.extend_zero.symm) (γ.extend_extends' t).symm, fun t' => ?_⟩⟩
    dsimp [Path.truncateOfLE, Path.truncate]
    exact γ.extend_extends' ⟨min (max t'.1 0) t.1, by simp [t.2.1, t.2.2]⟩ ▸ hγ _⟩

中文:
定理 isPathConnected_pathComponentIn
  条件: (h : x in F)
  结论: 是道路连通 (pathComponentIn F x)
  证明: ⟨x, mem_pathComponentIn_self h, fun _ ⟨γ, hγ⟩ => by
    refine ⟨γ, fun t =>
      ⟨(γ.truncateOfLE t.2.1).cast (γ.extend_zero.symm) (γ.extend_extends' t).symm, fun t' => ?_⟩⟩
    dsimp [Path.truncateOfLE, Path.truncate]
    exact γ.extend_extends' ⟨min (max t'.1 0) t.1, by simp [t.2.1, t.2.2]⟩ ▸ hγ _⟩

Depends on / 依赖: Path.truncate, Path.truncateOfLE, extend_extends, extend_zero, extend_zero.symm, mem_pathComponentIn_self, truncate, truncateOfLE
-/
theorem isPathConnected_pathComponentIn (h : x in F) : IsPathConnected (pathComponentIn F x) :=
  ⟨x, mem_pathComponentIn_self h, fun _ ⟨γ, hγ⟩ => by
    refine ⟨γ, fun t =>
      ⟨(γ.truncateOfLE t.2.1).cast (γ.extend_zero.symm) (γ.extend_extends' t).symm, fun t' => ?_⟩⟩
    dsimp [Path.truncateOfLE, Path.truncate]
    exact γ.extend_extends' ⟨min (max t'.1 0) t.1, by simp [t.2.1, t.2.2]⟩ ▸ hγ _⟩

/--
theorem `isPathConnected_pathComponent` / 定理 `isPathConnected_pathComponent`

English:
theorem isPathConnected_pathComponent
  statement: IsPathConnected (pathComponent x)
  proof: by
  rw [← pathComponentIn_univ]
  exact isPathConnected_pathComponentIn (mem_univ x)

中文:
定理 isPathConnected_pathComponent
  结论: 是道路连通 (pathComponent x)
  证明: by
  rw [← pathComponentIn_univ]
  exact isPathConnected_pathComponentIn (mem_univ x)

Depends on / 依赖: isPathConnected_pathComponentIn, mem_univ, pathComponentIn_univ
-/
theorem isPathConnected_pathComponent : IsPathConnected (pathComponent x) := by
  rw [← pathComponentIn_univ]
  exact isPathConnected_pathComponentIn (mem_univ x)

/--
theorem `IsPathConnected.union` / 定理 `IsPathConnected.union`

English:
theorem IsPathConnected.union
  statement: {U V : Set X} (hU : IsPathConnected U) (hV : IsPathConnected V)
  proof: by
  rcases hUV with ⟨x, xU, xV⟩
  use x, Or.inl xU
  rintro y (yU | yV)
  · exact (hU.joinedIn x xU y yU).mono subset_union_left
  · exact (hV.joinedIn x xV y yV).mono subset_union_right

中文:
定理 是道路连通.union
  结论: {U V : 集合 X} (hU : 是道路连通 U) (hV : 是道路连通 V)
  证明: by
  rcases hUV with ⟨x, xU, xV⟩
  use x, Or.inl xU
  rintro y (yU | yV)
  · exact (hU.joinedIn x xU y yU).mono subset_union_left
  · exact (hV.joinedIn x xV y yV).mono subset_union_right

Depends on / 依赖: Or.inl, hU.joinedIn, hV.joinedIn, joinedIn, subset_union_left, subset_union_right
-/
theorem IsPathConnected.union {U V : Set X} (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : (U inter V).Nonempty) : IsPathConnected (U union V) := by
  rcases hUV with ⟨x, xU, xV⟩
  use x, Or.inl xU
  rintro y (yU | yV)
  · exact (hU.joinedIn x xU y yU).mono subset_union_left
  · exact (hV.joinedIn x xV y yV).mono subset_union_right

/--
theorem `IsPathConnected.preimage_coe` / 定理 `IsPathConnected.preimage_coe`

English:
theorem IsPathConnected.preimage_coe
  given: {U W : Set X} (hW : IsPathConnected W) (hWU : W subseteq U)
  proof: by
  rwa [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_val, inter_eq_right.2 hWU]

中文:
定理 是道路连通.preimage_coe
  条件: {U W : 集合 X} (hW : 是道路连通 W) (hWU : W subseteq U)
  证明: by
  rwa [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_val, inter_eq_right.2 hWU]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.isPathConnected_iff, Subtype, Subtype.image_preimage_val, image_preimage_val, inter_eq_right, isPathConnected_iff, subtypeVal
-/
theorem IsPathConnected.preimage_coe {U W : Set X} (hW : IsPathConnected W) (hWU : W subseteq U) :
    IsPathConnected (((↑) : U -> X) ⁻¹' W) := by
  rwa [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_val, inter_eq_right.2 hWU]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsPathConnected.exists_path_through_family` / 定理 `IsPathConnected.exists_path_through_family`

English:
theorem IsPathConnected.exists_path_through_family
  statement: {n : Nat}
  proof: by
  cases p using snocCases with | _ p x => ?_
  simp only [forall_fin_succ', snoc_castSucc, snoc_last, Path.cast_coe,
    Path.target_mem_range, and_true] at hp ⊢
  obtain ⟨hp, hx⟩ := hp
  induction p using snocInduction generalizing x with
  | elim0 =>
    simp only [snoc_zero]
    use Path.refl x
    simp [hx]
  | @snoc n p y hp₂ =>
    simp only [forall_fin_succ', snoc_castSucc, snoc_last, snoc_apply_zero, Path.cast_coe] at hp ⊢
    obtain ⟨hp, hy⟩ := hp
    specialize hp₂ y hp hy
    obtain ⟨γ₀, hγ₀s, hγ₀p⟩ := hp₂
    obtain ⟨γ₁, hγ₁⟩ := h.joinedIn y hy x hx
    rw [← range_subset_iff] at hγ₁
    use γ₀.trans γ₁
    simp only [Path.trans_range, mem_union, Path.source_mem_range, or_true, and_true,
      union_subset_iff]
    tauto

中文:
定理 是道路连通.存在_path_through_family
  结论: {n : 自然数}
  证明: by
  cases p using snocCases with | _ p x => ?_
  simp only [forall_fin_succ', snoc_castSucc, snoc_last, Path.cast_coe,
    Path.target_mem_range, and_true] at hp ⊢
  obtain ⟨hp, hx⟩ := hp
  induction p using snocInduction generalizing x with
  | elim0 =>
    simp only [snoc_zero]
    use Path.refl x
    simp [hx]
  | @snoc n p y hp₂ =>
    simp only [forall_fin_succ', snoc_castSucc, snoc_last, snoc_apply_zero, Path.cast_coe] at hp ⊢
    obtain ⟨hp, hy⟩ := hp
    specialize hp₂ y hp hy
    obtain ⟨γ₀, hγ₀s, hγ₀p⟩ := hp₂
    obtain ⟨γ₁, hγ₁⟩ := h.joinedIn y hy x hx
    rw [← range_subset_iff] at hγ₁
    use γ₀.trans γ₁
    simp only [Path.trans_range, mem_union, Path.source_mem_range, or_true, and_true,
      union_subset_iff]
    tauto

Depends on / 依赖: Path.cast_coe, Path.refl, Path.target_mem_range, and_true, cast_coe, forall_fin_succ, generalizing, snocCases, snocInduction, snoc_apply_zero, snoc_castSucc, snoc_last, snoc_zero, specialize, target_mem_range
-/
theorem IsPathConnected.exists_path_through_family {n : Nat}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) -> X) (hp : forall i, p i in s) :
    exists γ : Path (p 0) (p (last n)), range γ subseteq s ∧ forall i, p i in range γ := by
  cases p using snocCases with | _ p x => ?_
  simp only [forall_fin_succ', snoc_castSucc, snoc_last, Path.cast_coe,
    Path.target_mem_range, and_true] at hp ⊢
  obtain ⟨hp, hx⟩ := hp
  induction p using snocInduction generalizing x with
  | elim0 =>
    simp only [snoc_zero]
    use Path.refl x
    simp [hx]
  | @snoc n p y hp₂ =>
    simp only [forall_fin_succ', snoc_castSucc, snoc_last, snoc_apply_zero, Path.cast_coe] at hp ⊢
    obtain ⟨hp, hy⟩ := hp
    specialize hp₂ y hp hy
    obtain ⟨γ₀, hγ₀s, hγ₀p⟩ := hp₂
    obtain ⟨γ₁, hγ₁⟩ := h.joinedIn y hy x hx
    rw [← range_subset_iff] at hγ₁
    use γ₀.trans γ₁
    simp only [Path.trans_range, mem_union, Path.source_mem_range, or_true, and_true,
      union_subset_iff]
    tauto

/--
theorem `IsPathConnected.exists_path_through_family'` / 定理 `IsPathConnected.exists_path_through_family'`

English:
theorem IsPathConnected.exists_path_through_family'
  statement: {n : Nat}
  proof: by
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
  rcases hγ with ⟨h₁, h₂⟩
  simp only [range, mem_ofPred_eq] at h₂
  rw [range_subset_iff] at h₁
  choose! t ht using h₂
  exact ⟨γ, t, h₁, ht⟩

中文:
定理 是道路连通.存在_path_through_family'
  结论: {n : 自然数}
  证明: by
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
  rcases hγ with ⟨h₁, h₂⟩
  simp only [range, mem_ofPred_eq] at h₂
  rw [range_subset_iff] at h₁
  choose! t ht using h₂
  exact ⟨γ, t, h₁, ht⟩

Depends on / 依赖: exists_path_through_family, h.exists_path_through_family, mem_ofPred_eq, range_subset_iff
-/
theorem IsPathConnected.exists_path_through_family' {n : Nat}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) -> X) (hp : forall i, p i in s) :
    exists (γ : Path (p 0) (p (last n))) (t : Fin (n + 1) -> I), (forall t, γ t in s) ∧ forall i, γ (t i) = p i := by
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
  rcases hγ with ⟨h₁, h₂⟩
  simp only [range, mem_ofPred_eq] at h₂
  rw [range_subset_iff] at h₁
  choose! t ht using h₂
  exact ⟨γ, t, h₁, ht⟩

/-! ### Path connected spaces -/


/-- A topological space is path-connected if it is non-empty and every two points can be
joined by a continuous path. -/
@[mk_iff]
/--
Definition of `PathConnectedSpace` / `PathConnectedSpace` 的定义

English:
class PathConnectedSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (2):
    - nonempty : Nonempty X
    - joined : forall x y : X, Joined x y

中文:
类 道路连通空间
  参数: (X : 类型) [拓扑空间 X]
  公理与运算 (2 个):
    - nonempty : 非空 X
    - joined : 对任意 x y : X, Joined x y
-/
class PathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- A path-connected space must be nonempty. -/
  nonempty : Nonempty X
  /-- Any two points in a path-connected space must be joined by a continuous path. -/
  joined : forall x y : X, Joined x y

/--
theorem `pathConnectedSpace_iff_zerothHomotopy` / 定理 `pathConnectedSpace_iff_zerothHomotopy`

English:
theorem pathConnectedSpace_iff_zerothHomotopy
  proof: by
  let := pathSetoid X
  constructor
  · intro h
    refine ⟨(nonempty_quotient_iff _).mpr h.1, ⟨?_⟩⟩
    rintro ⟨x⟩ ⟨y⟩
    exact Quotient.sound (PathConnectedSpace.joined x y)
  · unfold ZerothHomotopy
    rintro ⟨h, h'⟩
exact ⟨(nonempty_quotient_iff _).mp h, fun x y => Quotient.exact Subsingleton.elim ⟦x⟧ ⟦y⟧⟩

中文:
定理 pathConnectedSpace_iff_zerothHomotopy
  证明: by
  let := pathSetoid X
  constructor
  · intro h
    refine ⟨(nonempty_quotient_iff _).mpr h.1, ⟨?_⟩⟩
    rintro ⟨x⟩ ⟨y⟩
    exact Quotient.sound (PathConnectedSpace.joined x y)
  · unfold ZerothHomotopy
    rintro ⟨h, h'⟩
exact ⟨(nonempty_quotient_iff _).mp h, fun x y => Quotient.exact Subsingleton.elim ⟦x⟧ ⟦y⟧⟩

Depends on / 依赖: PathConnectedSpace, PathConnectedSpace.joined, Quotient, Quotient.exact, Quotient.sound, Subsingleton, Subsingleton.elim, ZerothHomotopy, joined, nonempty_quotient_iff, pathSetoid
-/
theorem pathConnectedSpace_iff_zerothHomotopy :
    PathConnectedSpace X ↔ Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) := by
  let := pathSetoid X
  constructor
  · intro h
    refine ⟨(nonempty_quotient_iff _).mpr h.1, ⟨?_⟩⟩
    rintro ⟨x⟩ ⟨y⟩
    exact Quotient.sound (PathConnectedSpace.joined x y)
  · unfold ZerothHomotopy
    rintro ⟨h, h'⟩
exact ⟨(nonempty_quotient_iff _).mp h, fun x y => Quotient.exact Subsingleton.elim ⟦x⟧ ⟦y⟧⟩

namespace PathConnectedSpace

variable [PathConnectedSpace X]

/--
Definition of `somePath` / `somePath` 的定义

English:
definition somePath
  signature: (x y : X)
  body: Nonempty.some (joined x y)

中文:
定义 somePath
  签名: (x y : X)
  定义体: Nonempty.some (joined x y)

Depends on / 依赖: Nonempty, Nonempty.some, joined
-/
def somePath (x y : X) : Path x y :=
  Nonempty.some (joined x y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (ZerothHomotopy X)
  body: (pathConnectedSpace_iff_zerothHomotopy.1 inferInstance).2

中文:
实例 :
  签名: 子单例 (ZerothHomotopy X)
  定义体: (pathConnectedSpace_iff_zerothHomotopy.1 inferInstance).2

Depends on / 依赖: pathConnectedSpace_iff_zerothHomotopy
-/
instance : Subsingleton (ZerothHomotopy X) :=
  (pathConnectedSpace_iff_zerothHomotopy.1 inferInstance).2

end PathConnectedSpace

/--
theorem `pathConnectedSpace_iff_univ` / 定理 `pathConnectedSpace_iff_univ`

English:
theorem pathConnectedSpace_iff_univ
  statement: PathConnectedSpace X ↔ IsPathConnected (univ : Set X)
  proof: by
  simp [pathConnectedSpace_iff, isPathConnected_iff, nonempty_iff_univ_nonempty]

中文:
定理 pathConnectedSpace_iff_univ
  结论: 道路连通空间 X ↔ 是道路连通 (univ : 集合 X)
  证明: by
  simp [pathConnectedSpace_iff, isPathConnected_iff, nonempty_iff_univ_nonempty]

Depends on / 依赖: isPathConnected_iff, nonempty_iff_univ_nonempty, pathConnectedSpace_iff
-/
theorem pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X) := by
  simp [pathConnectedSpace_iff, isPathConnected_iff, nonempty_iff_univ_nonempty]

/--
theorem `isPathConnected_iff_pathConnectedSpace` / 定理 `isPathConnected_iff_pathConnectedSpace`

English:
theorem isPathConnected_iff_pathConnectedSpace
  statement: IsPathConnected F ↔ PathConnectedSpace F
  proof: by
  rw [pathConnectedSpace_iff_univ]; rw [IsInducing.subtypeVal.isPathConnected_iff]; rw [image_univ]; rw [Subtype.range_val_subtype]; rw [ofPred_mem_eq]

中文:
定理 isPathConnected_iff_pathConnectedSpace
  结论: 是道路连通 F ↔ 道路连通空间 F
  证明: by
  rw [pathConnectedSpace_iff_univ]; rw [IsInducing.subtypeVal.isPathConnected_iff]; rw [image_univ]; rw [Subtype.range_val_subtype]; rw [ofPred_mem_eq]

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.isPathConnected_iff, Subtype, Subtype.range_val_subtype, image_univ, isPathConnected_iff, ofPred_mem_eq, pathConnectedSpace_iff_univ, range_val_subtype, subtypeVal
-/
theorem isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace F := by
  rw [pathConnectedSpace_iff_univ]; rw [IsInducing.subtypeVal.isPathConnected_iff]; rw [image_univ]; rw [Subtype.range_val_subtype]; rw [ofPred_mem_eq]

/--
theorem `isPathConnected_univ` / 定理 `isPathConnected_univ`

English:
theorem isPathConnected_univ
  given: [PathConnectedSpace X]
  statement: IsPathConnected (univ : Set X)
  proof: pathConnectedSpace_iff_univ.mp inferInstance

中文:
定理 isPathConnected_univ
  条件: [道路连通空间 X]
  结论: 是道路连通 (univ : 集合 X)
  证明: pathConnectedSpace_iff_univ.mp inferInstance

Depends on / 依赖: pathConnectedSpace_iff_univ, pathConnectedSpace_iff_univ.mp
-/
theorem isPathConnected_univ [PathConnectedSpace X] : IsPathConnected (univ : Set X) :=
  pathConnectedSpace_iff_univ.mp inferInstance

/--
theorem `isPathConnected_range` / 定理 `isPathConnected_range`

English:
theorem isPathConnected_range
  given: [PathConnectedSpace X] {f : X -> Y} (hf : Continuous f)
  proof: by
  rw [← image_univ]
  exact isPathConnected_univ.image hf

中文:
定理 isPathConnected_range
  条件: [道路连通空间 X] {f : X -> Y} (hf : 连续 f)
  证明: by
  rw [← image_univ]
  exact isPathConnected_univ.image hf

Depends on / 依赖: image_univ, isPathConnected_univ, isPathConnected_univ.image
-/
theorem isPathConnected_range [PathConnectedSpace X] {f : X -> Y} (hf : Continuous f) :
    IsPathConnected (range f) := by
  rw [← image_univ]
  exact isPathConnected_univ.image hf

/--
theorem `Function.Surjective.pathConnectedSpace` / 定理 `Function.Surjective.pathConnectedSpace`

English:
theorem Function.Surjective.pathConnectedSpace
  statement: [PathConnectedSpace X]
  proof: by
  rw [pathConnectedSpace_iff_univ]; rw [← hf.range_eq]
  exact isPathConnected_range hf'

中文:
定理 函数.满射.pathConnectedSpace
  结论: [道路连通空间 X]
  证明: by
  rw [pathConnectedSpace_iff_univ]; rw [← hf.range_eq]
  exact isPathConnected_range hf'

Depends on / 依赖: hf.range_eq, isPathConnected_range, pathConnectedSpace_iff_univ, range_eq
-/
theorem Function.Surjective.pathConnectedSpace [PathConnectedSpace X]
    {f : X -> Y} (hf : Surjective f) (hf' : Continuous f) : PathConnectedSpace Y := by
  rw [pathConnectedSpace_iff_univ]; rw [← hf.range_eq]
  exact isPathConnected_range hf'

/--
Instance `Quotient.instPathConnectedSpace` / 实例 `Quotient.instPathConnectedSpace`

English:
instance Quotient.instPathConnectedSpace
  signature: {s : Setoid X} [PathConnectedSpace X]
  body: Quotient.mk'_surjective.pathConnectedSpace continuous_coinduced_rng

中文:
实例 商.instPathConnectedSpace
  签名: {s : 集合等价关系 X} [道路连通空间 X]
  定义体: Quotient.mk'_surjective.pathConnectedSpace continuous_coinduced_rng

Depends on / 依赖: Quotient, Quotient.mk, _surjective, _surjective.pathConnectedSpace, continuous_coinduced_rng, pathConnectedSpace
-/
instance Quotient.instPathConnectedSpace {s : Setoid X} [PathConnectedSpace X] :
    PathConnectedSpace (Quotient s) :=
  Quotient.mk'_surjective.pathConnectedSpace continuous_coinduced_rng

/--
Instance `Real.instPathConnectedSpace` / 实例 `Real.instPathConnectedSpace`

English:
instance Real.instPathConnectedSpace
  signature: : PathConnectedSpace Real where
  body: ⟨⟨⟨fun (t : I) => (1 - t) * x + t * y, by fun_prop⟩, by simp, by simp⟩⟩
  nonempty := inferInstance

中文:
实例 实数.instPathConnectedSpace
  签名: : 道路连通空间 实数 where
  定义体: ⟨⟨⟨fun (t : I) => (1 - t) * x + t * y, by fun_prop⟩, by simp, by simp⟩⟩
  nonempty := inferInstance

Depends on / 依赖: fun_prop
-/
instance Real.instPathConnectedSpace : PathConnectedSpace Real where
  joined x y := ⟨⟨⟨fun (t : I) => (1 - t) * x + t * y, by fun_prop⟩, by simp, by simp⟩⟩
  nonempty := inferInstance

/-! ### Products and pi types -/

section Prod

variable {s : Set X} {t : Set Y}

/--
theorem `Joined.prod` / 定理 `Joined.prod`

English:
theorem Joined.prod
  given: {x₁ x₂ : X} {y₁ y₂ : Y} (hx : Joined x₁ x₂) (hy : Joined y₁ y₂)
  proof: ⟨hx.somePath.prod hy.somePath⟩

中文:
定理 Joined.乘积
  条件: {x₁ x₂ : X} {y₁ y₂ : Y} (hx : Joined x₁ x₂) (hy : Joined y₁ y₂)
  证明: ⟨hx.somePath.prod hy.somePath⟩

Depends on / 依赖: hx.somePath.prod, hy.somePath, somePath
-/
theorem Joined.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : Joined x₁ x₂) (hy : Joined y₁ y₂) :
    Joined (x₁, y₁) (x₂, y₂) :=
  ⟨hx.somePath.prod hy.somePath⟩

/--
theorem `JoinedIn.prod` / 定理 `JoinedIn.prod`

English:
theorem JoinedIn.prod
  given: {x₁ x₂ : X} {y₁ y₂ : Y} (hx : JoinedIn s x₁ x₂) (hy : JoinedIn t y₁ y₂)
  proof: ⟨hx.somePath.prod hy.somePath, by simp⟩

中文:
定理 JoinedIn.乘积
  条件: {x₁ x₂ : X} {y₁ y₂ : Y} (hx : JoinedIn s x₁ x₂) (hy : JoinedIn t y₁ y₂)
  证明: ⟨hx.somePath.prod hy.somePath, by simp⟩

Depends on / 依赖: hx.somePath.prod, hy.somePath, somePath
-/
theorem JoinedIn.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : JoinedIn s x₁ x₂) (hy : JoinedIn t y₁ y₂) :
    JoinedIn (s ×ˢ t) (x₁, y₁) (x₂, y₂) :=
  ⟨hx.somePath.prod hy.somePath, by simp⟩

/--
theorem `pathComponent_prod` / 定理 `pathComponent_prod`

English:
theorem pathComponent_prod
  given: (x : X) (y : Y)
  proof: by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, mem_pathComponent_iff]
  exact ⟨fun h => ⟨h.map continuous_fst, h.map continuous_snd⟩, fun ⟨h₁, h₂⟩ => h₁.prod h₂⟩

中文:
定理 pathComponent_prod
  条件: (x : X) (y : Y)
  证明: by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, mem_pathComponent_iff]
  exact ⟨fun h => ⟨h.map continuous_fst, h.map continuous_snd⟩, fun ⟨h₁, h₂⟩ => h₁.prod h₂⟩

Depends on / 依赖: Set.mem_prod, continuous_fst, continuous_snd, h.map, mem_pathComponent_iff, mem_prod
-/
theorem pathComponent_prod (x : X) (y : Y) :
    pathComponent (x, y) = pathComponent x ×ˢ pathComponent y := by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, mem_pathComponent_iff]
  exact ⟨fun h => ⟨h.map continuous_fst, h.map continuous_snd⟩, fun ⟨h₁, h₂⟩ => h₁.prod h₂⟩

/--
theorem `IsPathConnected.prod` / 定理 `IsPathConnected.prod`

English:
theorem IsPathConnected.prod
  given: (hs : IsPathConnected s) (ht : IsPathConnected t)
  proof: by
  rw [isPathConnected_iff]
  refine ⟨hs.nonempty.prod ht.nonempty, fun (x₁, y₁) ⟨hx₁, hy₁⟩ (x₂, y₂) ⟨hx₂, hy₂⟩ => ?_⟩
.prod ht.joinedIn y₁ hy₁ y₂ hy₂ exact hs.joinedIn x₁ hx₁ x₂ hx₂

中文:
定理 是道路连通.乘积
  条件: (hs : 是道路连通 s) (ht : 是道路连通 t)
  证明: by
  rw [isPathConnected_iff]
  refine ⟨hs.nonempty.prod ht.nonempty, fun (x₁, y₁) ⟨hx₁, hy₁⟩ (x₂, y₂) ⟨hx₂, hy₂⟩ => ?_⟩
.prod ht.joinedIn y₁ hy₁ y₂ hy₂ exact hs.joinedIn x₁ hx₁ x₂ hx₂

Depends on / 依赖: hs.joinedIn, hs.nonempty.prod, ht.joinedIn, ht.nonempty, isPathConnected_iff, joinedIn, nonempty
-/
theorem IsPathConnected.prod (hs : IsPathConnected s) (ht : IsPathConnected t) :
    IsPathConnected (s ×ˢ t) := by
  rw [isPathConnected_iff]
  refine ⟨hs.nonempty.prod ht.nonempty, fun (x₁, y₁) ⟨hx₁, hy₁⟩ (x₂, y₂) ⟨hx₂, hy₂⟩ => ?_⟩
.prod ht.joinedIn y₁ hy₁ y₂ hy₂ exact hs.joinedIn x₁ hx₁ x₂ hx₂

/--
Instance `Prod.instPathConnectedSpace` / 实例 `Prod.instPathConnectedSpace`

English:
instance Prod.instPathConnectedSpace
  signature: [PathConnectedSpace X] [PathConnectedSpace Y]
  body: by
  rw [pathConnectedSpace_iff_univ]; rw [← Set.univ_prod_univ]
  exact isPathConnected_univ.prod isPathConnected_univ

中文:
实例 积类型.instPathConnectedSpace
  签名: [道路连通空间 X] [道路连通空间 Y]
  定义体: by
  rw [pathConnectedSpace_iff_univ]; rw [← Set.univ_prod_univ]
  exact isPathConnected_univ.prod isPathConnected_univ

Depends on / 依赖: Set.univ_prod_univ, isPathConnected_univ, isPathConnected_univ.prod, pathConnectedSpace_iff_univ, univ_prod_univ
-/
instance Prod.instPathConnectedSpace [PathConnectedSpace X] [PathConnectedSpace Y] :
    PathConnectedSpace (X × Y) := by
  rw [pathConnectedSpace_iff_univ]; rw [← Set.univ_prod_univ]
  exact isPathConnected_univ.prod isPathConnected_univ

end Prod

section Pi

variable {Z : ι -> Type*} [forall i, TopologicalSpace (Z i)]

/--
theorem `Joined.pi` / 定理 `Joined.pi`

English:
theorem Joined.pi
  given: {x y : forall i, Z i} (h : forall i, Joined (x i) (y i))
  statement: Joined x y
  proof: ⟨.pi fun i => (h i).somePath⟩

中文:
定理 Joined.pi
  条件: {x y : 对任意 i, Z i} (h : 对任意 i, Joined (x i) (y i))
  结论: Joined x y
  证明: ⟨.pi fun i => (h i).somePath⟩

Depends on / 依赖: somePath
-/
theorem Joined.pi {x y : forall i, Z i} (h : forall i, Joined (x i) (y i)) : Joined x y :=
  ⟨.pi fun i => (h i).somePath⟩

/--
theorem `JoinedIn.pi` / 定理 `JoinedIn.pi`

English:
theorem JoinedIn.pi
  statement: {s : forall i, Set (Z i)} {x y : forall i, Z i}
  proof: ⟨.pi (fun i => (h i).somePath), by simp⟩

中文:
定理 JoinedIn.pi
  结论: {s : 对任意 i, 集合 (Z i)} {x y : 对任意 i, Z i}
  证明: ⟨.pi (fun i => (h i).somePath), by simp⟩

Depends on / 依赖: somePath
-/
theorem JoinedIn.pi {s : forall i, Set (Z i)} {x y : forall i, Z i}
    (h : forall i, JoinedIn (s i) (x i) (y i)) : JoinedIn (Set.univ.pi s) x y :=
  ⟨.pi (fun i => (h i).somePath), by simp⟩

/--
theorem `pathComponent_pi` / 定理 `pathComponent_pi`

English:
theorem pathComponent_pi
  given: (x : forall i, Z i)
  proof: by
  ext y
  simp only [Set.mem_univ_pi, mem_pathComponent_iff]
  exact ⟨fun h i => h.map (continuous_apply i), fun h => .pi h⟩

中文:
定理 pathComponent_pi
  条件: (x : 对任意 i, Z i)
  证明: by
  ext y
  simp only [Set.mem_univ_pi, mem_pathComponent_iff]
  exact ⟨fun h i => h.map (continuous_apply i), fun h => .pi h⟩

Depends on / 依赖: Set.mem_univ_pi, continuous_apply, h.map, mem_pathComponent_iff, mem_univ_pi
-/
theorem pathComponent_pi (x : forall i, Z i) :
    pathComponent x = Set.univ.pi fun i => pathComponent (x i) := by
  ext y
  simp only [Set.mem_univ_pi, mem_pathComponent_iff]
  exact ⟨fun h i => h.map (continuous_apply i), fun h => .pi h⟩

/--
theorem `IsPathConnected.pi` / 定理 `IsPathConnected.pi`

English:
theorem IsPathConnected.pi
  given: {s : forall i, Set (Z i)} (h : forall i, IsPathConnected (s i))
  proof: by
  choose x hx hjoin using h
  exact ⟨x, by simpa, fun y hy => .pi fun i => hjoin i (by grind)⟩

中文:
定理 是道路连通.pi
  条件: {s : 对任意 i, 集合 (Z i)} (h : 对任意 i, 是道路连通 (s i))
  证明: by
  choose x hx hjoin using h
  exact ⟨x, by simpa, fun y hy => .pi fun i => hjoin i (by grind)⟩
-/
theorem IsPathConnected.pi {s : forall i, Set (Z i)} (h : forall i, IsPathConnected (s i)) :
    IsPathConnected (Set.univ.pi s) := by
  choose x hx hjoin using h
  exact ⟨x, by simpa, fun y hy => .pi fun i => hjoin i (by grind)⟩

/--
Instance `Pi.instPathConnectedSpace` / 实例 `Pi.instPathConnectedSpace`

English:
instance Pi.instPathConnectedSpace
  signature: [forall i, PathConnectedSpace (Z i)]
  body: by
  rw [pathConnectedSpace_iff_univ]; rw [← Set.pi_univ]
  exact .pi fun _ => isPathConnected_univ

中文:
实例 依赖函数类型.instPathConnectedSpace
  签名: [对任意 i, 道路连通空间 (Z i)]
  定义体: by
  rw [pathConnectedSpace_iff_univ]; rw [← Set.pi_univ]
  exact .pi fun _ => isPathConnected_univ

Depends on / 依赖: Set.pi_univ, isPathConnected_univ, pathConnectedSpace_iff_univ, pi_univ
-/
instance Pi.instPathConnectedSpace [forall i, PathConnectedSpace (Z i)] :
    PathConnectedSpace (forall i, Z i) := by
  rw [pathConnectedSpace_iff_univ]; rw [← Set.pi_univ]
  exact .pi fun _ => isPathConnected_univ

end Pi

/--
theorem `pathConnectedSpace_iff_eq` / 定理 `pathConnectedSpace_iff_eq`

English:
theorem pathConnectedSpace_iff_eq
  statement: PathConnectedSpace X ↔ exists x : X, pathComponent x = univ
  proof: by
  simp [pathConnectedSpace_iff_univ, isPathConnected_iff_eq]

中文:
定理 pathConnectedSpace_iff_eq
  结论: 道路连通空间 X ↔ 存在 x : X, pathComponent x = univ
  证明: by
  simp [pathConnectedSpace_iff_univ, isPathConnected_iff_eq]

Depends on / 依赖: isPathConnected_iff_eq, pathConnectedSpace_iff_univ
-/
theorem pathConnectedSpace_iff_eq : PathConnectedSpace X ↔ exists x : X, pathComponent x = univ := by
  simp [pathConnectedSpace_iff_univ, isPathConnected_iff_eq]

-- see Note [lower instance priority]
instance (priority := 100) PathConnectedSpace.connectedSpace [PathConnectedSpace X] :
    ConnectedSpace X := by
  rw [connectedSpace_iff_connectedComponent]
  rcases isPathConnected_iff_eq.mp (pathConnectedSpace_iff_univ.mp ‹_›) with ⟨x, _x_in, hx⟩
  use x
  rw [← univ_subset_iff]
  exact (by simpa using hx : pathComponent x = univ) ▸ pathComponent_subset_component x

/--
theorem `IsPathConnected.isConnected` / 定理 `IsPathConnected.isConnected`

English:
theorem IsPathConnected.isConnected
  given: (hF : IsPathConnected F)
  statement: IsConnected F
  proof: by
  rw [isConnected_iff_connectedSpace]
  rw [isPathConnected_iff_pathConnectedSpace] at hF
  exact @PathConnectedSpace.connectedSpace _ _ hF

中文:
定理 是道路连通.isConnected
  条件: (hF : 是道路连通 F)
  结论: 是连通 F
  证明: by
  rw [isConnected_iff_connectedSpace]
  rw [isPathConnected_iff_pathConnectedSpace] at hF
  exact @PathConnectedSpace.connectedSpace _ _ hF

Depends on / 依赖: PathConnectedSpace, PathConnectedSpace.connectedSpace, connectedSpace, isConnected_iff_connectedSpace, isPathConnected_iff_pathConnectedSpace
-/
theorem IsPathConnected.isConnected (hF : IsPathConnected F) : IsConnected F := by
  rw [isConnected_iff_connectedSpace]
  rw [isPathConnected_iff_pathConnectedSpace] at hF
  exact @PathConnectedSpace.connectedSpace _ _ hF

namespace PathConnectedSpace

variable [PathConnectedSpace X]

/--
theorem `exists_path_through_family` / 定理 `exists_path_through_family`

English:
theorem exists_path_through_family
  given: {n : Nat} (p : Fin (n + 1) -> X)
  proof: by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family p fun _i => True.intro with ⟨γ, -, h⟩
  exact ⟨γ, h⟩

中文:
定理 存在_path_through_family
  条件: {n : 自然数} (p : 有限集 (n + 1) -> X)
  证明: by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family p fun _i => True.intro with ⟨γ, -, h⟩
  exact ⟨γ, h⟩

Depends on / 依赖: IsPathConnected, True.intro, exists_path_through_family, infer_instance, pathConnectedSpace_iff_univ, pathConnectedSpace_iff_univ.mp, this.exists_path_through_family
-/
theorem exists_path_through_family {n : Nat} (p : Fin (n + 1) -> X) :
    exists γ : Path (p 0) (p (last n)), forall i, p i in range γ := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family p fun _i => True.intro with ⟨γ, -, h⟩
  exact ⟨γ, h⟩

/--
theorem `exists_path_through_family'` / 定理 `exists_path_through_family'`

English:
theorem exists_path_through_family'
  given: {n : Nat} (p : Fin (n + 1) -> X)
  proof: by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family' p fun _i => True.intro with ⟨γ, t, -, h⟩
  exact ⟨γ, t, h⟩

中文:
定理 存在_path_through_family'
  条件: {n : 自然数} (p : 有限集 (n + 1) -> X)
  证明: by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family' p fun _i => True.intro with ⟨γ, t, -, h⟩
  exact ⟨γ, t, h⟩

Depends on / 依赖: IsPathConnected, True.intro, exists_path_through_family, infer_instance, pathConnectedSpace_iff_univ, pathConnectedSpace_iff_univ.mp, this.exists_path_through_family
-/
theorem exists_path_through_family' {n : Nat} (p : Fin (n + 1) -> X) :
    exists (γ : Path (p 0) (p (last n))) (t : Fin (n + 1) -> I), forall i, γ (t i) = p i := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family' p fun _i => True.intro with ⟨γ, t, -, h⟩
  exact ⟨γ, t, h⟩

end PathConnectedSpace

/--
theorem `ZerothHomotopy.preimage_singleton_eq_pathComponent` / 定理 `ZerothHomotopy.preimage_singleton_eq_pathComponent`

English:
theorem ZerothHomotopy.preimage_singleton_eq_pathComponent
  given: (x : X)
  proof: by
  ext y
  rw [mem_preimage]; rw [mem_singleton_iff]; rw [eq_comm]; rw [mem_pathComponent_iff]
  exact Quotient.eq

中文:
定理 ZerothHomotopy.preimage_singleton_eq_pathComponent
  条件: (x : X)
  证明: by
  ext y
  rw [mem_preimage]; rw [mem_singleton_iff]; rw [eq_comm]; rw [mem_pathComponent_iff]
  exact Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq, eq_comm, mem_pathComponent_iff, mem_preimage, mem_singleton_iff
-/
theorem ZerothHomotopy.preimage_singleton_eq_pathComponent (x : X) :
    ZerothHomotopy.mk ⁻¹' {.mk x} = pathComponent x := by
  ext y
  rw [mem_preimage]; rw [mem_singleton_iff]; rw [eq_comm]; rw [mem_pathComponent_iff]
  exact Quotient.eq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: X] : CompactSpace ZerothHomotopy X
  body: Quotient.compactSpace

中文:
实例 [紧空间
  签名: X] : 紧空间 ZerothHomotopy X
  定义体: Quotient.compactSpace

Depends on / 依赖: Quotient, Quotient.compactSpace, compactSpace
-/
instance [CompactSpace X] : CompactSpace ZerothHomotopy X := Quotient.compactSpace
