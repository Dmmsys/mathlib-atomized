/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous bundled maps

In this file we define the type `ContinuousMap` of continuous bundled maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/

@[expose] public section


open Function Topology

section ContinuousMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β]
variable [ContinuousMapClass F α β]

/--
theorem `map_continuousAt` / 定理 `map_continuousAt`

English:
theorem map_continuousAt
  given: (f : F) (a : α)
  statement: ContinuousAt f a
  proof: (map_continuous f).continuousAt

中文:
定理 map_continuousAt
  条件: (f : F) (a : α)
  结论: ContinuousAt f a
  证明: (map_continuous f).continuousAt

Depends on / 依赖: continuousAt, map_continuous
-/
theorem map_continuousAt (f : F) (a : α) : ContinuousAt f a :=
  (map_continuous f).continuousAt

/--
theorem `map_continuousWithinAt` / 定理 `map_continuousWithinAt`

English:
theorem map_continuousWithinAt
  given: (f : F) (s : Set α) (a : α)
  statement: ContinuousWithinAt f s a
  proof: (map_continuous f).continuousWithinAt

中文:
定理 map_continuousWithinAt
  条件: (f : F) (s : 集合 α) (a : α)
  结论: ContinuousWithinAt f s a
  证明: (map_continuous f).continuousWithinAt

Depends on / 依赖: continuousWithinAt, map_continuous
-/
theorem map_continuousWithinAt (f : F) (s : Set α) (a : α) : ContinuousWithinAt f s a :=
  (map_continuous f).continuousWithinAt

end ContinuousMapClass

/-! ### Continuous maps -/


namespace ContinuousMap

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

variable {f g : C(α, β)}

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: (f : C(α, β)) (x : α)
  statement: ContinuousAt f x
  proof: map_continuousAt f x

中文:
定理 continuousAt
  条件: (f : C(α, β)) (x : α)
  结论: ContinuousAt f x
  证明: map_continuousAt f x
-/
protected theorem continuousAt (f : C(α, β)) (x : α) : ContinuousAt f x :=
  map_continuousAt f x

/--
theorem `map_specializes` / 定理 `map_specializes`

English:
theorem map_specializes
  given: (f : C(α, β)) {x y : α} (h : x ⤳ y)
  statement: f x ⤳ f y
  proof: h.map f.2

中文:
定理 map_specializes
  条件: (f : C(α, β)) {x y : α} (h : x ⤳ y)
  结论: f x ⤳ f y
  证明: h.map f.2

Depends on / 依赖: h.map
-/
theorem map_specializes (f : C(α, β)) {x y : α} (h : x ⤳ y) : f x ⤳ f y :=
  h.map f.2

section DiscreteTopology
variable [DiscreteTopology α]

/--
The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
/--
Definition of `equivFnOfDiscrete` / `equivFnOfDiscrete` 的定义

English:
definition equivFnOfDiscrete
  signature: : C(α, β) ≃ (α -> β)
  body: ⟨fun f => f,
    fun f => ⟨f, continuous_of_discreteTopology⟩,
    fun _ => by ext; rfl,
    fun _ => by ext; rfl⟩

中文:
定义 equivFnOfDiscrete
  签名: : C(α, β) ≃ (α -> β)
  定义体: ⟨fun f => f,
    fun f => ⟨f, continuous_of_discreteTopology⟩,
    fun _ => by ext; rfl,
    fun _ => by ext; rfl⟩

Depends on / 依赖: continuous_of_discreteTopology
-/
def equivFnOfDiscrete : C(α, β) ≃ (α -> β) :=
  ⟨fun f => f,
    fun f => ⟨f, continuous_of_discreteTopology⟩,
    fun _ => by ext; rfl,
    fun _ => by ext; rfl⟩

/--
lemma `coe_equivFnOfDiscrete` / 引理 `coe_equivFnOfDiscrete`

English:
lemma coe_equivFnOfDiscrete
  statement: ⇑equivFnOfDiscrete = (DFunLike.coe : C(α, β) -> α -> β)
  proof: rfl

中文:
引理 coe_equivFnOfDiscrete
  结论: ⇑equivFnOfDiscrete = (依赖函数状.coe : C(α, β) -> α -> β)
  证明: rfl
-/
@[simp] lemma coe_equivFnOfDiscrete : ⇑equivFnOfDiscrete = (DFunLike.coe : C(α, β) -> α -> β) := rfl

/--
lemma `equivFnOfDiscrete_symm_apply` / 引理 `equivFnOfDiscrete_symm_apply`

English:
lemma equivFnOfDiscrete_symm_apply
  given: (f : α -> β)
  statement: equivFnOfDiscrete.symm f = f
  proof: rfl

中文:
引理 equivFnOfDiscrete_symm_apply
  条件: (f : α -> β)
  结论: equivFnOfDiscrete.symm f = f
  证明: rfl
-/
@[simp] lemma equivFnOfDiscrete_symm_apply (f : α -> β) : equivFnOfDiscrete.symm f = f := rfl

end DiscreteTopology

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : C(α, α) where
  body: id

@[simp, norm_cast]

中文:
定义 id
  签名: : C(α, α) where
  定义体: id

@[simp, norm_cast]
-/
protected def id : C(α, α) where
  toFun := id

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(ContinuousMap.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(连续映射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(ContinuousMap.id α) = id :=
  rfl

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (b : β)
  body: fun _ : α => b

@[simp]

中文:
定义 const
  签名: (b : β)
  定义体: fun _ : α => b

@[simp]
-/
def const (b : β) : C(α, β) where
  toFun := fun _ : α => b

@[simp]
/--
theorem `coe_const` / 定理 `coe_const`

English:
theorem coe_const
  given: (b : β)
  statement: ⇑(const α b) = Function.const α b
  proof: rfl

中文:
定理 coe_const
  条件: (b : β)
  结论: ⇑(const α b) = 函数.const α b
  证明: rfl
-/
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

/-- `Function.const α b` as a bundled continuous function of `b`. -/
@[simps -fullyApplied]
/--
Definition of `constPi` / `constPi` 的定义

English:
definition constPi
  signature: : C(β, α -> β) where
  body: Function.const α b

中文:
定义 constPi
  签名: : C(β, α -> β) where
  定义体: Function.const α b

Depends on / 依赖: Function, Function.const
-/
def constPi : C(β, α -> β) where
  toFun b := Function.const α b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: β] : Inhabited C(α, β)
  body: ⟨const α default⟩

中文:
实例 [可居
  签名: β] : 可居 C(α, β)
  定义体: ⟨const α default⟩
-/
instance [Inhabited β] : Inhabited C(α, β) :=
  ⟨const α default⟩

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: ContinuousMap.id α a = a
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (a : α)
  结论: 连续映射.id α a = a
  证明: rfl

@[simp]
-/
theorem id_apply (a : α) : ContinuousMap.id α a = a :=
  rfl

@[simp]
/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  given: (b : β) (a : α)
  statement: const α b a = b
  proof: rfl

中文:
定理 const_apply
  条件: (b : β) (a : α)
  结论: const α b a = b
  证明: rfl
-/
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

/-- The composition of continuous maps, as a continuous map. -/
@[implicit_reducible]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : C(β, γ)) (g : C(α, β))
  body: f ∘ g

@[simp]

中文:
定义 comp
  签名: (f : C(β, γ)) (g : C(α, β))
  定义体: f ∘ g

@[simp]
-/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where
  toFun := f ∘ g

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : C(β, γ)) (g : C(α, β))
  statement: ⇑(comp f g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : C(β, γ)) (g : C(α, β))
  结论: ⇑(comp f g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : C(β, γ)) (g : C(α, β)) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : C(β, γ)) (g : C(α, β)) (a : α)
  statement: comp f g a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : C(β, γ)) (g : C(α, β)) (a : α)
  结论: comp f g a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β))
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β))
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β)) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : C(α, β))
  statement: (ContinuousMap.id _).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : C(α, β))
  结论: (连续映射.id _).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : C(α, β)) : (ContinuousMap.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : C(α, β))
  statement: f.comp (ContinuousMap.id _) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : C(α, β))
  结论: f.comp (连续映射.id _) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : C(α, β)) : f.comp (ContinuousMap.id _) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `const_comp` / 定理 `const_comp`

English:
theorem const_comp
  given: (c : γ) (f : C(α, β))
  statement: (const β c).comp f = const α c
  proof: ext fun _ => rfl

@[simp]

中文:
定理 const_comp
  条件: (c : γ) (f : C(α, β))
  结论: (const β c).comp f = const α c
  证明: ext fun _ => rfl

@[simp]
-/
theorem const_comp (c : γ) (f : C(α, β)) : (const β c).comp f = const α c :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_const` / 定理 `comp_const`

English:
theorem comp_const
  given: (f : C(β, γ)) (b : β)
  statement: f.comp (const α b) = const α (f b)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_const
  条件: (f : C(β, γ)) (b : β)
  结论: f.comp (const α b) = const α (f b)
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_const (f : C(β, γ)) (b : β) : f.comp (const α b) = const α (f b) :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g)
  proof: ⟨fun h => ext hg.forall.2 DFunLike.ext_iff.1 h, congr_arg (ContinuousMap.comp · g)⟩

@[simp]

中文:
定理 cancel_right
  条件: {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : 满射 g)
  证明: ⟨fun h => ext hg.forall.2 DFunLike.ext_iff.1 h, congr_arg (ContinuousMap.comp · g)⟩

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.comp, DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hg.forall
-/
theorem cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
⟨fun h => ext hg.forall.2 DFunLike.ext_iff.1 h, congr_arg (ContinuousMap.comp · g)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f)
  proof: ⟨fun h => ext fun a => hf by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : 单射 f)
  证明: ⟨fun h => ext fun a => hf by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
⟨fun h => ext fun a => hf by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] [Nontrivial β] : Nontrivial C(α, β)
  body: ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
⟨const _ b₁, const _ b₂, fun h => hb DFunLike.congr_fun h Classical.arbitrary α⟩⟩

中文:
实例 [非空
  签名: α] [非平凡 β] : 非平凡 C(α, β)
  定义体: ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
⟨const _ b₁, const _ b₂, fun h => hb DFunLike.congr_fun h Classical.arbitrary α⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, DFunLike, DFunLike.congr_fun, arbitrary, congr_fun, exists_pair_ne
-/
instance [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
⟨const _ b₁, const _ b₂, fun h => hb DFunLike.congr_fun h Classical.arbitrary α⟩⟩

/-- The bijection `C(X₁, Y₁) ≃ C(X₂, Y₂)` induced by homeomorphisms
`e : X₁ ≃ₜ X₂` and `e' : Y₁ ≃ₜ Y₂`. -/
@[simps]
/--
Definition of `_root_.Homeomorph.continuousMapCongr` / `_root_.Homeomorph.continuousMapCongr` 的定义

English:
definition _root_.Homeomorph.continuousMapCongr
  signature: {X₁ X₂ Y₁ Y₂ : Type*}
  body: ContinuousMap.comp ⟨_, e'.continuous⟩ (f.comp ⟨_, e.symm.continuous⟩)
  invFun g := ContinuousMap.comp ⟨_, e'.symm.continuous⟩ (g.comp ⟨_, e.continuous⟩)
  left_inv _ := by aesop
  right_inv _ := by aesop

中文:
定义 _root_.同胚.continuousMapCongr
  签名: {X₁ X₂ Y₁ Y₂ : 类型}
  定义体: ContinuousMap.comp ⟨_, e'.continuous⟩ (f.comp ⟨_, e.symm.continuous⟩)
  invFun g := ContinuousMap.comp ⟨_, e'.symm.continuous⟩ (g.comp ⟨_, e.continuous⟩)
  left_inv _ := by aesop
  right_inv _ := by aesop

Depends on / 依赖: ContinuousMap, ContinuousMap.comp, continuous, e.symm.continuous, f.comp
-/
def _root_.Homeomorph.continuousMapCongr {X₁ X₂ Y₁ Y₂ : Type*}
    [TopologicalSpace X₁] [TopologicalSpace X₂]
    [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    (e : X₁ ≃ₜ X₂) (e' : Y₁ ≃ₜ Y₂) :
    C(X₁, Y₁) ≃ C(X₂, Y₂) where
  toFun f := ContinuousMap.comp ⟨_, e'.continuous⟩ (f.comp ⟨_, e.symm.continuous⟩)
  invFun g := ContinuousMap.comp ⟨_, e'.symm.continuous⟩ (g.comp ⟨_, e.continuous⟩)
  left_inv _ := by aesop
  right_inv _ := by aesop

section Prod

variable {α₁ α₂ β₁ β₂ : Type*} [TopologicalSpace α₁] [TopologicalSpace α₂] [TopologicalSpace β₁]
  [TopologicalSpace β₂]

/-- `Prod.fst : (x, y) ↦ x` as a bundled continuous map. -/
@[simps -fullyApplied]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : C(α × β, α) where
  body: Prod.fst

中文:
定义 fst
  签名: : C(α × β, α) where
  定义体: Prod.fst

Depends on / 依赖: Prod.fst
-/
def fst : C(α × β, α) where
  toFun := Prod.fst

/-- `Prod.snd : (x, y) ↦ y` as a bundled continuous map. -/
@[simps -fullyApplied]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : C(α × β, β) where
  body: Prod.snd

中文:
定义 snd
  签名: : C(α × β, β) where
  定义体: Prod.snd

Depends on / 依赖: Prod.snd
-/
def snd : C(α × β, β) where
  toFun := Prod.snd

/--
Definition of `prodMk` / `prodMk` 的定义

English:
definition prodMk
  signature: (f : C(α, β₁)) (g : C(α, β₂))
  body: (f x, g x)

中文:
定义 prodMk
  签名: (f : C(α, β₁)) (g : C(α, β₂))
  定义体: (f x, g x)
-/
def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where
  toFun x := (f x, g x)

/-- Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x, g y)`. -/
@[simps]
/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f : C(α₁, α₂)) (g : C(β₁, β₂))
  body: Prod.map f g

@[simp]

中文:
定义 prodMap
  签名: (f : C(α₁, α₂)) (g : C(β₁, β₂))
  定义体: Prod.map f g

@[simp]

Depends on / 依赖: Prod.map
-/
def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂) where
  toFun := Prod.map f g

@[simp]
/--
theorem `prod_eval` / 定理 `prod_eval`

English:
theorem prod_eval
  given: (f : C(α, β₁)) (g : C(α, β₂)) (a : α)
  statement: (prodMk f g) a = (f a, g a)
  proof: rfl

中文:
定理 prod_eval
  条件: (f : C(α, β₁)) (g : C(α, β₂)) (a : α)
  结论: (prodMk f g) a = (f a, g a)
  证明: rfl
-/
theorem prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g a) :=
  rfl

/-- `Prod.swap` bundled as a `ContinuousMap`. -/
@[simps!]
/--
Definition of `prodSwap` / `prodSwap` 的定义

English:
definition prodSwap
  signature: : C(α × β, β × α)
  body: .prodMk .snd .fst

中文:
定义 prodSwap
  签名: : C(α × β, β × α)
  定义体: .prodMk .snd .fst

Depends on / 依赖: prodMk
-/
def prodSwap : C(α × β, β × α) := .prodMk .snd .fst

end Prod

section Sigma

variable {I A : Type*} {X : I -> Type*} [TopologicalSpace A] [forall i, TopologicalSpace (X i)]

/-- `Sigma.mk i` as a bundled continuous map. -/
@[simps apply]
/--
Definition of `sigmaMk` / `sigmaMk` 的定义

English:
definition sigmaMk
  signature: (i : I)
  body: Sigma.mk i

中文:
定义 sigmaMk
  签名: (i : I)
  定义体: Sigma.mk i

Depends on / 依赖: Sigma.mk
-/
def sigmaMk (i : I) : C(X i, Σ i, X i) where
  toFun := Sigma.mk i

/--
To give a continuous map out of a disjoint union, it suffices to give a continuous map out of
each term. This is `Sigma.uncurry` for continuous maps.
-/
@[simps]
/--
Definition of `sigma` / `sigma` 的定义

English:
definition sigma
  signature: (f : forall i, C(X i, A))
  body: f ig.fst ig.snd
  continuous_toFun := by continuity

中文:
定义 sigma
  签名: (f : 对任意 i, C(X i, A))
  定义体: f ig.fst ig.snd
  continuous_toFun := by continuity

Depends on / 依赖: ig.fst, ig.snd
-/
def sigma (f : forall i, C(X i, A)) : C((Σ i, X i), A) where
  toFun ig := f ig.fst ig.snd
  continuous_toFun := by continuity

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term. This is a version of `Equiv.piCurry` for continuous maps.
-/
@[simps]
/--
Definition of `sigmaEquiv` / `sigmaEquiv` 的定义

English:
definition sigmaEquiv
  signature: : (forall i, C(X i, A)) ≃ C((Σ i, X i), A) where
  body: sigma
  invFun f i := f.comp (sigmaMk i)

中文:
定义 sigmaEquiv
  签名: : (对任意 i, C(X i, A)) ≃ C((Σ i, X i), A) where
  定义体: sigma
  invFun f i := f.comp (sigmaMk i)
-/
def sigmaEquiv : (forall i, C(X i, A)) ≃ C((Σ i, X i), A) where
  toFun := sigma
  invFun f i := f.comp (sigmaMk i)

end Sigma

section Pi

variable {I A : Type*} {X Y : I -> Type*} [TopologicalSpace A] [forall i, TopologicalSpace (X i)]
  [forall i, TopologicalSpace (Y i)]

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (f : forall i, C(A, X i))
  body: f i a

@[simp]

中文:
定义 pi
  签名: (f : 对任意 i, C(A, X i))
  定义体: f i a

@[simp]
-/
def pi (f : forall i, C(A, X i)) : C(A, forall i, X i) where
  toFun (a : A) (i : I) := f i a

@[simp]
/--
theorem `pi_eval` / 定理 `pi_eval`

English:
theorem pi_eval
  given: (f : forall i, C(A, X i)) (a : A)
  statement: (pi f) a = fun i : I => (f i) a
  proof: rfl

中文:
定理 pi_eval
  条件: (f : 对任意 i, C(A, X i)) (a : A)
  结论: (pi f) a = fun i : I => (f i) a
  证明: rfl
-/
theorem pi_eval (f : forall i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) a :=
  rfl

/-- Evaluation at point as a bundled continuous map. -/
@[simps -fullyApplied]
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (i : I)
  body: Function.eval i

中文:
定义 eval
  签名: (i : I)
  定义体: Function.eval i

Depends on / 依赖: Function, Function.eval
-/
def eval (i : I) : C(forall j, X j, X i) where
  toFun := Function.eval i

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term
-/
@[simps]
/--
Definition of `piEquiv` / `piEquiv` 的定义

English:
definition piEquiv
  signature: : (forall i, C(A, X i)) ≃ C(A, forall i, X i) where
  body: pi
  invFun f i := (eval i).comp f

中文:
定义 piEquiv
  签名: : (对任意 i, C(A, X i)) ≃ C(A, 对任意 i, X i) where
  定义体: pi
  invFun f i := (eval i).comp f
-/
def piEquiv : (forall i, C(A, X i)) ≃ C(A, forall i, X i) where
  toFun := pi
  invFun f i := (eval i).comp f

/-- Combine a collection of bundled continuous maps `C(X i, Y i)` into a bundled continuous map
`C(∀ i, X i, ∀ i, Y i)`. -/
@[simps!]
/--
Definition of `piMap` / `piMap` 的定义

English:
definition piMap
  signature: (f : forall i, C(X i, Y i))
  body: .pi fun i => (f i).comp (eval i)

中文:
定义 piMap
  签名: (f : 对任意 i, C(X i, Y i))
  定义体: .pi fun i => (f i).comp (eval i)
-/
def piMap (f : forall i, C(X i, Y i)) : C((i : I) -> X i, (i : I) -> Y i) :=
  .pi fun i => (f i).comp (eval i)

/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: {ι : Type*} (φ : ι -> I)
  body: ⟨_, Pi.continuous_precomp' φ⟩

中文:
定义 precomp
  签名: {ι : 类型} (φ : ι -> I)
  定义体: ⟨_, Pi.continuous_precomp' φ⟩

Depends on / 依赖: Pi.continuous_precomp, continuous_precomp
-/
def precomp {ι : Type*} (φ : ι -> I) : C((i : I) -> X i, (i : ι) -> X (φ i)) :=
  ⟨_, Pi.continuous_precomp' φ⟩

end Pi

section Restrict

variable (s : Set α)

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (f : C(α, β))
  body: f ∘ ((↑) : s -> α)

@[simp]

中文:
定义 restrict
  签名: (f : C(α, β))
  定义体: f ∘ ((↑) : s -> α)

@[simp]
-/
def restrict (f : C(α, β)) : C(s, β) where
  toFun := f ∘ ((↑) : s -> α)

@[simp]
/--
theorem `coe_restrict` / 定理 `coe_restrict`

English:
theorem coe_restrict
  given: (f : C(α, β))
  statement: ⇑(f.restrict s) = s.domRestrict f
  proof: rfl

@[simp]

中文:
定理 coe_restrict
  条件: (f : C(α, β))
  结论: ⇑(f.restrict s) = s.domRestrict f
  证明: rfl

@[simp]
-/
theorem coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = s.domRestrict f :=
  rfl

@[simp]
/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  given: (f : C(α, β)) (s : Set α) (x : s)
  statement: f.restrict s x = f x
  proof: rfl

@[simp]

中文:
定理 restrict_apply
  条件: (f : C(α, β)) (s : 集合 α) (x : s)
  结论: f.restrict s x = f x
  证明: rfl

@[simp]
-/
theorem restrict_apply (f : C(α, β)) (s : Set α) (x : s) : f.restrict s x = f x :=
  rfl

@[simp]
/--
theorem `restrict_apply_mk` / 定理 `restrict_apply_mk`

English:
theorem restrict_apply_mk
  given: (f : C(α, β)) (s : Set α) (x : α) (hx : x in s)
  proof: rfl

中文:
定理 restrict_apply_mk
  条件: (f : C(α, β)) (s : 集合 α) (x : α) (hx : x in s)
  证明: rfl
-/
theorem restrict_apply_mk (f : C(α, β)) (s : Set α) (x : α) (hx : x in s) :
    f.restrict s ⟨x, hx⟩ = f x :=
  rfl

/--
theorem `injective_restrict` / 定理 `injective_restrict`

English:
theorem injective_restrict
  given: [T2Space β] {s : Set α} (hs : Dense s)
  proof: fun f g h =>
DFunLike.ext' (map_continuous f).ext_on hs (map_continuous g)
Set.domRestrict_eq_domRestrict_iff.1 congr_arg DFunLike.coe h

中文:
定理 injective_restrict
  条件: [T2空间 β] {s : 集合 α} (hs : 稠密 s)
  证明: fun f g h =>
DFunLike.ext' (map_continuous f).ext_on hs (map_continuous g)
Set.domRestrict_eq_domRestrict_iff.1 congr_arg DFunLike.coe h
-/
theorem injective_restrict [T2Space β] {s : Set α} (hs : Dense s) :
    Injective (restrict s : C(α, β) -> C(s, β)) := fun f g h =>
DFunLike.ext' (map_continuous f).ext_on hs (map_continuous g)
Set.domRestrict_eq_domRestrict_iff.1 congr_arg DFunLike.coe h

/-- The restriction of a continuous map to the preimage of a set. -/
@[simps]
/--
Definition of `restrictPreimage` / `restrictPreimage` 的定义

English:
definition restrictPreimage
  signature: (f : C(α, β)) (s : Set β)
  body: ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun _ =>
    (map_continuousAt f _).restrictPreimage⟩

中文:
定义 restrictPreimage
  签名: (f : C(α, β)) (s : 集合 β)
  定义体: ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun _ =>
    (map_continuousAt f _).restrictPreimage⟩

Depends on / 依赖: continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, map_continuousAt, restrictPreimage, s.restrictPreimage
-/
def restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s) :=
  ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun _ =>
    (map_continuousAt f _).restrictPreimage⟩

end Restrict

section mkD

/--
Definition of `mkD` / `mkD` 的定义

English:
definition mkD
  signature: (f : α -> β) (default : C(α, β))
  body: open scoped Classical in
  if h : Continuous f then ⟨_, h⟩ else default

中文:
定义 mkD
  签名: (f : α -> β) (default : C(α, β))
  定义体: open scoped Classical in
  if h : Continuous f then ⟨_, h⟩ else default

Depends on / 依赖: Classical, Continuous, scoped
-/
noncomputable def mkD (f : α -> β) (default : C(α, β)) : C(α, β) :=
  open scoped Classical in
  if h : Continuous f then ⟨_, h⟩ else default

/--
lemma `mkD_of_continuous` / 引理 `mkD_of_continuous`

English:
lemma mkD_of_continuous
  given: {f : α -> β} {g : C(α, β)} (hf : Continuous f)
  proof: by
  simp only [mkD, hf, ↓reduceDIte]

中文:
引理 mkD_of_continuous
  条件: {f : α -> β} {g : C(α, β)} (hf : 连续 f)
  证明: by
  simp only [mkD, hf, ↓reduceDIte]

Depends on / 依赖: reduceDIte
-/
lemma mkD_of_continuous {f : α -> β} {g : C(α, β)} (hf : Continuous f) :
    mkD f g = ⟨f, hf⟩ := by
  simp only [mkD, hf, ↓reduceDIte]

/--
lemma `mkD_of_not_continuous` / 引理 `mkD_of_not_continuous`

English:
lemma mkD_of_not_continuous
  given: {f : α -> β} {g : C(α, β)} (hf : ¬ Continuous f)
  proof: by
  simp only [mkD, hf, ↓reduceDIte]

中文:
引理 mkD_of_not_continuous
  条件: {f : α -> β} {g : C(α, β)} (hf : ¬ 连续 f)
  证明: by
  simp only [mkD, hf, ↓reduceDIte]

Depends on / 依赖: reduceDIte
-/
lemma mkD_of_not_continuous {f : α -> β} {g : C(α, β)} (hf : ¬ Continuous f) :
    mkD f g = g := by
  simp only [mkD, hf, ↓reduceDIte]

/--
lemma `mkD_apply_of_continuous` / 引理 `mkD_apply_of_continuous`

English:
lemma mkD_apply_of_continuous
  given: {f : α -> β} {g : C(α, β)} {x : α} (hf : Continuous f)
  proof: by
  rw [mkD_of_continuous hf]; rw [coe_mk]

中文:
引理 mkD_apply_of_continuous
  条件: {f : α -> β} {g : C(α, β)} {x : α} (hf : 连续 f)
  证明: by
  rw [mkD_of_continuous hf]; rw [coe_mk]

Depends on / 依赖: coe_mk, mkD_of_continuous
-/
lemma mkD_apply_of_continuous {f : α -> β} {g : C(α, β)} {x : α} (hf : Continuous f) :
    mkD f g x = f x := by
  rw [mkD_of_continuous hf]; rw [coe_mk]

/--
lemma `mkD_of_continuousOn` / 引理 `mkD_of_continuousOn`

English:
lemma mkD_of_continuousOn
  statement: {s : Set α} {f : α -> β} {g : C(s, β)}
  proof: mkD_of_continuous hf.domRestrict

中文:
引理 mkD_of_continuousOn
  结论: {s : 集合 α} {f : α -> β} {g : C(s, β)}
  证明: mkD_of_continuous hf.domRestrict

Depends on / 依赖: domRestrict, hf.domRestrict, mkD_of_continuous
-/
lemma mkD_of_continuousOn {s : Set α} {f : α -> β} {g : C(s, β)}
    (hf : ContinuousOn f s) :
    mkD (s.domRestrict f) g = ⟨s.domRestrict f, hf.domRestrict⟩ := mkD_of_continuous hf.domRestrict

/--
lemma `mkD_of_not_continuousOn` / 引理 `mkD_of_not_continuousOn`

English:
lemma mkD_of_not_continuousOn
  statement: {s : Set α} {f : α -> β} {g : C(s, β)}
  proof: by
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact mkD_of_not_continuous hf

中文:
引理 mkD_of_not_continuousOn
  结论: {s : 集合 α} {f : α -> β} {g : C(s, β)}
  证明: by
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact mkD_of_not_continuous hf

Depends on / 依赖: continuousOn_iff_continuous_domRestrict, mkD_of_not_continuous
-/
lemma mkD_of_not_continuousOn {s : Set α} {f : α -> β} {g : C(s, β)}
    (hf : ¬ ContinuousOn f s) :
    mkD (s.domRestrict f) g = g := by
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact mkD_of_not_continuous hf

/--
lemma `mkD_apply_of_continuousOn` / 引理 `mkD_apply_of_continuousOn`

English:
lemma mkD_apply_of_continuousOn
  statement: {s : Set α} {f : α -> β} {g : C(s, β)} {x : s}
  proof: by rw [mkD_of_continuousOn hf, coe_mk, Set.domRestrict_apply]

中文:
引理 mkD_apply_of_continuousOn
  结论: {s : 集合 α} {f : α -> β} {g : C(s, β)} {x : s}
  证明: by rw [mkD_of_continuousOn hf, coe_mk, Set.domRestrict_apply]

Depends on / 依赖: Set.domRestrict_apply, coe_mk, domRestrict_apply, mkD_of_continuousOn
-/
lemma mkD_apply_of_continuousOn {s : Set α} {f : α -> β} {g : C(s, β)} {x : s}
    (hf : ContinuousOn f s) :
    mkD (s.domRestrict f) g x = f x := by rw [mkD_of_continuousOn hf, coe_mk, Set.domRestrict_apply]

/--
lemma `mkD_eq_self` / 引理 `mkD_eq_self`

English:
lemma mkD_eq_self
  given: {f g : C(α, β)}
  statement: mkD f g = f
  proof: mkD_of_continuous f.continuous

中文:
引理 mkD_eq_self
  条件: {f g : C(α, β)}
  结论: mkD f g = f
  证明: mkD_of_continuous f.continuous

Depends on / 依赖: continuous, f.continuous, mkD_of_continuous
-/
lemma mkD_eq_self {f g : C(α, β)} : mkD f g = f :=
  mkD_of_continuous f.continuous

end mkD

section Gluing

variable {ι : Type*} (S : ι -> Set α) (φ : forall i : ι, C(S i, β))
  (hφ : forall (i j) (x : α) (hxi : x in S i) (hxj : x in S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : forall x : α, exists i, S i in 𝓝 x)

/--
Definition of `liftCover` / `liftCover` 的定义

English:
definition liftCover
  signature: : C(α, β)
  body: haveI H : ⋃ i, S i = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun x => (hS x).imp fun _ => mem_of_mem_nhds
mk (Set.liftCover S (fun i => φ i) hφ H) continuous_of_cover_nhds hS fun i => by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe]
      using map_continuous (φ i)

中文:
定义 liftCover
  签名: : C(α, β)
  定义体: haveI H : ⋃ i, S i = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun x => (hS x).imp fun _ => mem_of_mem_nhds
mk (Set.liftCover S (fun i => φ i) hφ H) continuous_of_cover_nhds hS fun i => by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe]
      using map_continuous (φ i)

Depends on / 依赖: Set.domRestrict, Set.iUnion_eq_univ_iff, Set.liftCover, Set.liftCover_coe, Set.univ, continuousOn_iff_continuous_domRestrict, continuous_of_cover_nhds, domRestrict, iUnion_eq_univ_iff, liftCover, liftCover_coe, map_continuous, mem_of_mem_nhds, unfoldPartialApp
-/
noncomputable def liftCover : C(α, β) :=
  haveI H : ⋃ i, S i = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun x => (hS x).imp fun _ => mem_of_mem_nhds
mk (Set.liftCover S (fun i => φ i) hφ H) continuous_of_cover_nhds hS fun i => by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe]
      using map_continuous (φ i)

variable {S φ hφ hS}

@[simp]
/--
theorem `liftCover_coe` / 定理 `liftCover_coe`

English:
theorem liftCover_coe
  given: {i : ι} (x : S i)
  statement: liftCover S φ hφ hS x = φ i x
  proof: by
  rw [liftCover]; rw [coe_mk]; rw [Set.liftCover_coe _]

@[simp]

中文:
定理 liftCover_coe
  条件: {i : ι} (x : S i)
  结论: liftCover S φ hφ hS x = φ i x
  证明: by
  rw [liftCover]; rw [coe_mk]; rw [Set.liftCover_coe _]

@[simp]

Depends on / 依赖: Set.liftCover_coe, coe_mk, liftCover, liftCover_coe
-/
theorem liftCover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x := by
  rw [liftCover]; rw [coe_mk]; rw [Set.liftCover_coe _]

@[simp]
/--
theorem `liftCover_restrict` / 定理 `liftCover_restrict`

English:
theorem liftCover_restrict
  given: {i : ι}
  statement: (liftCover S φ hφ hS).restrict (S i) = φ i
  proof: by
  ext
  simp only [restrict_apply, liftCover_coe]

中文:
定理 liftCover_restrict
  条件: {i : ι}
  结论: (liftCover S φ hφ hS).restrict (S i) = φ i
  证明: by
  ext
  simp only [restrict_apply, liftCover_coe]

Depends on / 依赖: liftCover_coe, restrict_apply
-/
theorem liftCover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i := by
  ext
  simp only [restrict_apply, liftCover_coe]

variable (A : Set (Set α)) (F : forall s in A, C(s, β))
  (hF : forall (s) (hs : s in A) (t) (ht : t in A) (x : α) (hxi : x in s) (hxj : x in t),
    F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : forall x : α, exists i in A, i in 𝓝 x)

/--
Definition of `liftCover'` / `liftCover'` 的定义

English:
definition liftCover'
  signature: : C(α, β)
  body: let F : forall i : A, C(i, β) := fun i => F i i.prop
  liftCover ((↑) : A -> Set α) F (fun i j => hF i i.prop j j.prop)
    fun x => let ⟨s, hs, hsx⟩ := hA x; ⟨⟨s, hs⟩, hsx⟩

中文:
定义 liftCover'
  签名: : C(α, β)
  定义体: let F : forall i : A, C(i, β) := fun i => F i i.prop
  liftCover ((↑) : A -> Set α) F (fun i j => hF i i.prop j j.prop)
    fun x => let ⟨s, hs, hsx⟩ := hA x; ⟨⟨s, hs⟩, hsx⟩

Depends on / 依赖: i.prop, j.prop, liftCover
-/
noncomputable def liftCover' : C(α, β) :=
  let F : forall i : A, C(i, β) := fun i => F i i.prop
  liftCover ((↑) : A -> Set α) F (fun i j => hF i i.prop j j.prop)
    fun x => let ⟨s, hs, hsx⟩ := hA x; ⟨⟨s, hs⟩, hsx⟩

variable {A F hF hA}

-- Porting note: did not need `by delta liftCover'; exact` in mathlib3; goal was
-- closed by `liftCover_coe x'`
-- Might be something to do with the `let`s in the definition of `liftCover'`?
@[simp]
/--
theorem `liftCover_coe'` / 定理 `liftCover_coe'`

English:
theorem liftCover_coe'
  given: {s : Set α} {hs : s in A} (x : s)
  statement: liftCover' A F hF hA x = F s hs x
  proof: let x' : ((↑) : A -> Set α) ⟨s, hs⟩ := x
  by delta liftCover'; exact ContinuousMap.liftCover_coe x'

@[simp]

中文:
定理 liftCover_coe'
  条件: {s : 集合 α} {hs : s in A} (x : s)
  结论: liftCover' A F hF hA x = F s hs x
  证明: let x' : ((↑) : A -> Set α) ⟨s, hs⟩ := x
  by delta liftCover'; exact ContinuousMap.liftCover_coe x'

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.liftCover_coe, liftCover, liftCover_coe
-/
theorem liftCover_coe' {s : Set α} {hs : s in A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : ((↑) : A -> Set α) ⟨s, hs⟩ := x
  by delta liftCover'; exact ContinuousMap.liftCover_coe x'

@[simp]
/--
theorem `liftCover_restrict'` / 定理 `liftCover_restrict'`

English:
theorem liftCover_restrict'
  given: {s : Set α} {hs : s in A}
  proof: ext liftCover_coe' (hF := hF) (hA := hA)

中文:
定理 liftCover_restrict'
  条件: {s : 集合 α} {hs : s in A}
  证明: ext liftCover_coe' (hF := hF) (hA := hA)

Depends on / 依赖: liftCover_coe
-/
theorem liftCover_restrict' {s : Set α} {hs : s in A} :
(liftCover' A F hF hA).restrict s = F s hs := ext liftCover_coe' (hF := hF) (hA := hA)

end Gluing

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {s t : Set α} (h : s subseteq t)
  body: Set.inclusion h
  continuous_toFun := continuous_inclusion h

中文:
定义 inclusion
  签名: {s t : 集合 α} (h : s subseteq t)
  定义体: Set.inclusion h
  continuous_toFun := continuous_inclusion h

Depends on / 依赖: Set.inclusion, inclusion
-/
def inclusion {s t : Set α} (h : s subseteq t) : C(s, t) where
  toFun := Set.inclusion h
  continuous_toFun := continuous_inclusion h

end ContinuousMap

section Lift

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)}

/-- `Setoid.quotientKerEquivOfRightInverse` as a homeomorphism. -/
@[simps!]
/--
Definition of `Function.RightInverse.homeomorph` / `Function.RightInverse.homeomorph` 的定义

English:
definition Function.RightInverse.homeomorph
  signature: {f' : C(Y, X)} (hf : Function.RightInverse f' f)
  body: Setoid.quotientKerEquivOfRightInverse _ _ hf
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr (map_continuous f)
  continuous_invFun := continuous_quotient_mk'.comp (map_continuous f')

中文:
定义 函数.右逆.homeomorph
  签名: {f' : C(Y, X)} (hf : 函数.右逆 f' f)
  定义体: Setoid.quotientKerEquivOfRightInverse _ _ hf
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr (map_continuous f)
  continuous_invFun := continuous_quotient_mk'.comp (map_continuous f')

Depends on / 依赖: Setoid, Setoid.quotientKerEquivOfRightInverse, quotientKerEquivOfRightInverse
-/
def Function.RightInverse.homeomorph {f' : C(Y, X)} (hf : Function.RightInverse f' f) :
    Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfRightInverse _ _ hf
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr (map_continuous f)
  continuous_invFun := continuous_quotient_mk'.comp (map_continuous f')

namespace Topology.IsQuotientMap

/--
The homeomorphism from the quotient of a quotient map to its codomain. This is
`Setoid.quotientKerEquivOfSurjective` as a homeomorphism.
-/
@[simps!]
/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: (hf : IsQuotientMap f)
  body: Setoid.quotientKerEquivOfSurjective _ hf.surjective
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr hf.continuous
  continuous_invFun := by
    rw [hf.continuous_iff]
    convert! continuous_quotient_mk'
    ext
    simp only [Equiv.invFun_as_coe, Function.comp_apply,
      (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq]
    rfl

中文:
定义 homeomorph
  签名: (hf : 是商映射 f)
  定义体: Setoid.quotientKerEquivOfSurjective _ hf.surjective
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr hf.continuous
  continuous_invFun := by
    rw [hf.continuous_iff]
    convert! continuous_quotient_mk'
    ext
    simp only [Equiv.invFun_as_coe, Function.comp_apply,
      (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq]
    rfl

Depends on / 依赖: Setoid, Setoid.quotientKerEquivOfSurjective, hf.surjective, quotientKerEquivOfSurjective, surjective
-/
noncomputable def homeomorph (hf : IsQuotientMap f) : Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfSurjective _ hf.surjective
  continuous_toFun := isQuotientMap_quot_mk.continuous_iff.mpr hf.continuous
  continuous_invFun := by
    rw [hf.continuous_iff]
    convert! continuous_quotient_mk'
    ext
    simp only [Equiv.invFun_as_coe, Function.comp_apply,
      (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq]
    rfl

variable (hf : IsQuotientMap f) (g : C(X, Z)) (h : Function.FactorsThrough g f)

/-- Descend a continuous map, which is constant on the fibres, along a quotient map. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : C(Y, Z) where
  body: ((fun i => Quotient.liftOn' i g (fun _ _ (hab : f _ = f _) => h hab)) :
    Quotient (Setoid.ker f) -> Z) ∘ hf.homeomorph.symm
  continuous_toFun := Continuous.comp (continuous_quot_lift _ g.2) (Homeomorph.continuous _)

中文:
定义 lift
  签名: : C(Y, Z) where
  定义体: ((fun i => Quotient.liftOn' i g (fun _ _ (hab : f _ = f _) => h hab)) :
    Quotient (Setoid.ker f) -> Z) ∘ hf.homeomorph.symm
  continuous_toFun := Continuous.comp (continuous_quot_lift _ g.2) (Homeomorph.continuous _)

Depends on / 依赖: Quotient, Quotient.liftOn, liftOn
-/
noncomputable def lift : C(Y, Z) where
  toFun := ((fun i => Quotient.liftOn' i g (fun _ _ (hab : f _ = f _) => h hab)) :
    Quotient (Setoid.ker f) -> Z) ∘ hf.homeomorph.symm
  continuous_toFun := Continuous.comp (continuous_quot_lift _ g.2) (Homeomorph.continuous _)

/--
The obvious triangle induced by `IsQuotientMap.lift` commutes:
```
     g
  X --→ Z
  | ↗
f | / hf.lift g h
  v /
  Y
```
-/
@[simp]
/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  statement: (hf.lift g h).comp f = g
  proof: by
  ext
  simpa using h (Function.rightInverse_surjInv _ _)

中文:
定理 lift_comp
  结论: (hf.lift g h).comp f = g
  证明: by
  ext
  simpa using h (Function.rightInverse_surjInv _ _)

Depends on / 依赖: Function, Function.rightInverse_surjInv, rightInverse_surjInv
-/
theorem lift_comp : (hf.lift g h).comp f = g := by
  ext
  simpa using h (Function.rightInverse_surjInv _ _)

/-- `IsQuotientMap.lift` as an equivalence. -/
@[simps]
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: : { g : C(X, Z) // Function.FactorsThrough g f} ≃ C(Y, Z) where
  body: hf.lift g g.prop
  invFun g := ⟨g.comp f, fun _ _ h => by simp only [ContinuousMap.comp_apply]; rw [h]⟩
  left_inv := by intro; simp
  right_inv := by
    intro g
    ext a
    simpa using congrArg g (Function.rightInverse_surjInv hf.surjective a)

中文:
定义 liftEquiv
  签名: : { g : C(X, Z) // 函数.FactorsThrough g f} ≃ C(Y, Z) where
  定义体: hf.lift g g.prop
  invFun g := ⟨g.comp f, fun _ _ h => by simp only [ContinuousMap.comp_apply]; rw [h]⟩
  left_inv := by intro; simp
  right_inv := by
    intro g
    ext a
    simpa using congrArg g (Function.rightInverse_surjInv hf.surjective a)

Depends on / 依赖: g.prop, hf.lift
-/
noncomputable def liftEquiv : { g : C(X, Z) // Function.FactorsThrough g f} ≃ C(Y, Z) where
  toFun g := hf.lift g g.prop
  invFun g := ⟨g.comp f, fun _ _ h => by simp only [ContinuousMap.comp_apply]; rw [h]⟩
  left_inv := by intro; simp
  right_inv := by
    intro g
    ext a
    simpa using congrArg g (Function.rightInverse_surjInv hf.surjective a)

end Topology.IsQuotientMap
end Lift

namespace Homeomorph

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
variable (f : α ≃ₜ β) (g : β ≃ₜ γ)

/--
Instance `instContinuousMapClass` / 实例 `instContinuousMapClass`

English:
instance instContinuousMapClass
  signature: : ContinuousMapClass (α ≃ₜ β) α β where
  body: f.continuous_toFun

@[simp]

中文:
实例 instContinuousMapClass
  签名: : 连续映射类 (α ≃ₜ β) α β where
  定义体: f.continuous_toFun

@[simp]

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance instContinuousMapClass : ContinuousMapClass (α ≃ₜ β) α β where
  map_continuous f := f.continuous_toFun

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: (Homeomorph.refl α : C(α, α)) = ContinuousMap.id α
  proof: rfl

@[simp]

中文:
定理 coe_refl
  结论: (同胚.refl α : C(α, α)) = 连续映射.id α
  证明: rfl

@[simp]
-/
theorem coe_refl : (Homeomorph.refl α : C(α, α)) = ContinuousMap.id α :=
  rfl

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  statement: (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f
  proof: rfl

中文:
定理 coe_trans
  结论: (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f
  证明: rfl
-/
theorem coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f :=
  rfl

/-- Left inverse to a continuous map from a homeomorphism, mirroring `Equiv.symm_comp_self`. -/
@[simp]
/--
theorem `symm_comp_toContinuousMap` / 定理 `symm_comp_toContinuousMap`

English:
theorem symm_comp_toContinuousMap
  proof: by
  rw [← coe_trans]; rw [self_trans_symm]; rw [coe_refl]

中文:
定理 symm_comp_toContinuousMap
  证明: by
  rw [← coe_trans]; rw [self_trans_symm]; rw [coe_refl]

Depends on / 依赖: coe_refl, coe_trans, self_trans_symm
-/
theorem symm_comp_toContinuousMap :
    (f.symm : C(β, α)).comp (f : C(α, β)) = ContinuousMap.id α := by
  rw [← coe_trans]; rw [self_trans_symm]; rw [coe_refl]

/-- Right inverse to a continuous map from a homeomorphism, mirroring `Equiv.self_comp_symm`. -/
@[simp]
/--
theorem `toContinuousMap_comp_symm` / 定理 `toContinuousMap_comp_symm`

English:
theorem toContinuousMap_comp_symm
  proof: by
  rw [← coe_trans]; rw [symm_trans_self]; rw [coe_refl]

中文:
定理 toContinuousMap_comp_symm
  证明: by
  rw [← coe_trans]; rw [symm_trans_self]; rw [coe_refl]

Depends on / 依赖: coe_refl, coe_trans, symm_trans_self
-/
theorem toContinuousMap_comp_symm :
    (f : C(α, β)).comp (f.symm : C(β, α)) = ContinuousMap.id β := by
  rw [← coe_trans]; rw [symm_trans_self]; rw [coe_refl]

end Homeomorph
