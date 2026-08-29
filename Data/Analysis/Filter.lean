/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Order.Filter.Cofinite

/-!
# Computational realization of filters (experimental)

This file provides infrastructure to compute with filters.

## Main declarations

* `CFilter`: Realization of a filter base. Note that this is in the generality of filters on
  lattices, while `Filter` is filters of sets (so corresponding to `CFilter (Set α) σ`).
* `Filter.Realizer`: Realization of a `Filter`. `CFilter` that generates the given filter.
-/

@[expose] public section


open Set Filter

-- TODO write doc strings
/--
Definition of `CFilter` / `CFilter` 的定义

English:
structure CFilter
  parameters: (α σ : Type*) [PartialOrder α]
  axioms and operations (5):
    - f : σ -> α
    - pt : σ
    - inf : σ -> σ -> σ
    - inf_le_left : forall a b : σ, f (inf a b) <= f a
    - inf_le_right : forall a b : σ, f (inf a b) <= f b

中文:
结构 CFilter
  参数: (α σ : 类型) [偏序 α]
  公理与运算 (5 个):
    - f : σ -> α
    - pt : σ
    - inf : σ -> σ -> σ
    - inf_le_left : 对任意 a b : σ, f (下确界 a b) <= f a
    - inf_le_right : 对任意 a b : σ, f (下确界 a b) <= f b

Depends on / 依赖: Nat.le_refl, _eq_none, getElem, l.length, le_refl, length, mem_iff_getElem
-/
structure CFilter (α σ : Type*) [PartialOrder α] where
  f : σ -> α
  pt : σ
  inf : σ -> σ -> σ
  inf_le_left : forall a b : σ, f (inf a b) <= f a
  inf_le_right : forall a b : σ, f (inf a b) <= f b

variable {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] [SemilatticeInf α] : Inhabited (CFilter α α)
  body: ⟨{ f := id
      pt := default
      inf := (· ⊓ ·)
      inf_le_left := fun _ _ => inf_le_left
      inf_le_right := fun _ _ => inf_le_right }⟩

中文:
实例 [可居
  签名: α] [SemilatticeInf α] : 可居 (CFilter α α)
  定义体: ⟨{ f := id
      pt := default
      inf := (· ⊓ ·)
      inf_le_left := fun _ _ => inf_le_left
      inf_le_right := fun _ _ => inf_le_right }⟩

Depends on / 依赖: inf_le_left, inf_le_right
-/
instance [Inhabited α] [SemilatticeInf α] : Inhabited (CFilter α α) :=
  ⟨{ f := id
      pt := default
      inf := (· ⊓ ·)
      inf_le_left := fun _ _ => inf_le_left
      inf_le_right := fun _ _ => inf_le_right }⟩

namespace CFilter

section

variable [PartialOrder α] (F : CFilter α σ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (CFilter α σ) fun _ => σ -> α
  body: ⟨CFilter.f⟩

中文:
实例 :
  签名: CoeFun (CFilter α σ) fun _ => σ -> α
  定义体: ⟨CFilter.f⟩

Depends on / 依赖: CFilter, CFilter.f
-/
instance : CoeFun (CFilter α σ) fun _ => σ -> α :=
  ⟨CFilter.f⟩

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f pt inf h₁ h₂ a)
  statement: (@CFilter.mk α σ _ f pt inf h₁ h₂) a = f a
  proof: rfl

中文:
定理 coe_mk
  条件: (f pt 下确界 h₁ h₂ a)
  结论: (@CFilter.mk α σ _ f pt 下确界 h₁ h₂) a = f a
  证明: rfl
-/
theorem coe_mk (f pt inf h₁ h₂ a) : (@CFilter.mk α σ _ f pt inf h₁ h₂) a = f a :=
  rfl

/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: (E : σ ≃ τ)

中文:
定义 ofEquiv
  签名: (E : σ ≃ τ)

Depends on / 依赖: E.symm
-/
def ofEquiv (E : σ ≃ τ) : CFilter α σ -> CFilter α τ
  | ⟨f, p, g, h₁, h₂⟩ =>
    { f := fun a => f (E.symm a)
      pt := E p
      inf := fun a b => E (g (E.symm a) (E.symm b))
      inf_le_left := fun a b => by simpa using h₁ (E.symm a) (E.symm b)
      inf_le_right := fun a b => by simpa using h₂ (E.symm a) (E.symm b) }

@[simp]
/--
theorem `ofEquiv_val` / 定理 `ofEquiv_val`

English:
theorem ofEquiv_val
  given: (E : σ ≃ τ) (F : CFilter α σ) (a : τ)
  statement: F.ofEquiv E a = F (E.symm a)
  proof: by
  cases F; rfl

中文:
定理 ofEquiv_val
  条件: (E : σ ≃ τ) (F : CFilter α σ) (a : τ)
  结论: F.ofEquiv E a = F (E.symm a)
  证明: by
  cases F; rfl
-/
theorem ofEquiv_val (E : σ ≃ τ) (F : CFilter α σ) (a : τ) : F.ofEquiv E a = F (E.symm a) := by
  cases F; rfl

end

/--
Definition of `toFilter` / `toFilter` 的定义

English:
definition toFilter
  signature: (F : CFilter (Set α) σ)
  body: { a | exists b, F b subseteq a }
  univ_sets := ⟨F.pt, subset_univ _⟩
  sets_of_superset := fun ⟨b, h⟩ s => ⟨b, Subset.trans h s⟩
  inter_sets := fun ⟨a, h₁⟩ ⟨b, h₂⟩ => ⟨F.inf a b,
    subset_inter (Subset.trans (F.inf_le_left _ _) h₁) (Subset.trans (F.inf_le_right _ _) h₂)⟩

@[simp]

中文:
定义 toFilter
  签名: (F : CFilter (集合 α) σ)
  定义体: { a | exists b, F b subseteq a }
  univ_sets := ⟨F.pt, subset_univ _⟩
  sets_of_superset := fun ⟨b, h⟩ s => ⟨b, Subset.trans h s⟩
  inter_sets := fun ⟨a, h₁⟩ ⟨b, h₂⟩ => ⟨F.inf a b,
    subset_inter (Subset.trans (F.inf_le_left _ _) h₁) (Subset.trans (F.inf_le_right _ _) h₂)⟩

@[simp]

Depends on / 依赖: subseteq
-/
def toFilter (F : CFilter (Set α) σ) : Filter α where
  sets := { a | exists b, F b subseteq a }
  univ_sets := ⟨F.pt, subset_univ _⟩
  sets_of_superset := fun ⟨b, h⟩ s => ⟨b, Subset.trans h s⟩
  inter_sets := fun ⟨a, h₁⟩ ⟨b, h₂⟩ => ⟨F.inf a b,
    subset_inter (Subset.trans (F.inf_le_left _ _) h₁) (Subset.trans (F.inf_le_right _ _) h₂)⟩

@[simp]
/--
theorem `mem_toFilter_sets` / 定理 `mem_toFilter_sets`

English:
theorem mem_toFilter_sets
  given: (F : CFilter (Set α) σ) {a : Set α}
  statement: a in F.toFilter ↔ exists b, F b subseteq a
  proof: Iff.rfl

中文:
定理 mem_toFilter_sets
  条件: (F : CFilter (集合 α) σ) {a : 集合 α}
  结论: a in F.toFilter ↔ 存在 b, F b subseteq a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toFilter_sets (F : CFilter (Set α) σ) {a : Set α} : a in F.toFilter ↔ exists b, F b subseteq a :=
  Iff.rfl

end CFilter

-- TODO write doc strings
/--
Definition of `Filter.Realizer` / `Filter.Realizer` 的定义

English:
structure Filter.Realizer
  parameters: (f : Filter α)
  axioms and operations (3):
    - σ : Type*
    - F : CFilter (Set α) σ
    - eq : F.toFilter = f

中文:
结构 滤子.实数izer
  参数: (f : 滤子 α)
  公理与运算 (3 个):
    - σ : 类型
    - F : CFilter (集合 α) σ
    - eq : F.toFilter = f
-/
structure Filter.Realizer (f : Filter α) where
  σ : Type*
  F : CFilter (Set α) σ
  eq : F.toFilter = f

/--
Definition of `CFilter.toRealizer` / `CFilter.toRealizer` 的定义

English:
definition CFilter.toRealizer
  signature: (F : CFilter (Set α) σ)
  body: ⟨σ, F, rfl⟩

中文:
定义 CFilter.to实数izer
  签名: (F : CFilter (集合 α) σ)
  定义体: ⟨σ, F, rfl⟩
-/
protected def CFilter.toRealizer (F : CFilter (Set α) σ) : F.toFilter.Realizer :=
  ⟨σ, F, rfl⟩

namespace Filter.Realizer

/--
theorem `mem_sets` / 定理 `mem_sets`

English:
theorem mem_sets
  given: {f : Filter α} (F : f.Realizer) {a : Set α}
  statement: a in f ↔ exists b, F.F b subseteq a
  proof: by
  cases F; subst f; rfl

中文:
定理 mem_sets
  条件: {f : 滤子 α} (F : f.实数izer) {a : 集合 α}
  结论: a in f ↔ 存在 b, F.F b subseteq a
  证明: by
  cases F; subst f; rfl
-/
theorem mem_sets {f : Filter α} (F : f.Realizer) {a : Set α} : a in f ↔ exists b, F.F b subseteq a := by
  cases F; subst f; rfl

/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {f g : Filter α} (e : f = g) (F : f.Realizer)
  body: ⟨F.σ, F.F, F.eq.trans e⟩

中文:
定义 ofEq
  签名: {f g : 滤子 α} (e : f = g) (F : f.实数izer)
  定义体: ⟨F.σ, F.F, F.eq.trans e⟩

Depends on / 依赖: F.eq.trans
-/
def ofEq {f g : Filter α} (e : f = g) (F : f.Realizer) : g.Realizer :=
  ⟨F.σ, F.F, F.eq.trans e⟩

/--
Definition of `ofFilter` / `ofFilter` 的定义

English:
definition ofFilter
  signature: (f : Filter α)
  body: ⟨f.sets,
    { f := Subtype.val
      pt := ⟨univ, univ_mem⟩
      inf := fun ⟨_, h₁⟩ ⟨_, h₂⟩ => ⟨_, inter_mem h₁ h₂⟩
      inf_le_left := fun ⟨_, _⟩ ⟨_, _⟩ => inter_subset_left
      inf_le_right := fun ⟨_, _⟩ ⟨_, _⟩ => inter_subset_right },
filter_eq Set.ext fun _ => by simp [exists_mem_subset_iff]⟩

中文:
定义 ofFilter
  签名: (f : 滤子 α)
  定义体: ⟨f.sets,
    { f := Subtype.val
      pt := ⟨univ, univ_mem⟩
      inf := fun ⟨_, h₁⟩ ⟨_, h₂⟩ => ⟨_, inter_mem h₁ h₂⟩
      inf_le_left := fun ⟨_, _⟩ ⟨_, _⟩ => inter_subset_left
      inf_le_right := fun ⟨_, _⟩ ⟨_, _⟩ => inter_subset_right },
filter_eq Set.ext fun _ => by simp [exists_mem_subset_iff]⟩

Depends on / 依赖: Set.ext, Subtype, Subtype.val, exists_mem_subset_iff, f.sets, filter_eq, inf_le_left, inf_le_right, inter_mem, inter_subset_left, inter_subset_right, univ_mem
-/
def ofFilter (f : Filter α) : f.Realizer :=
  ⟨f.sets,
    { f := Subtype.val
      pt := ⟨univ, univ_mem⟩
      inf := fun ⟨_, h₁⟩ ⟨_, h₂⟩ => ⟨_, inter_mem h₁ h₂⟩
      inf_le_left := fun ⟨_, _⟩ ⟨_, _⟩ => inter_subset_left
      inf_le_right := fun ⟨_, _⟩ ⟨_, _⟩ => inter_subset_right },
filter_eq Set.ext fun _ => by simp [exists_mem_subset_iff]⟩

/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ)
  body: ⟨τ, F.F.ofEquiv E, by
    refine Eq.trans ?_ F.eq
    exact filter_eq (Set.ext fun _ =>
      ⟨fun ⟨s, h⟩ => ⟨E.symm s, by simpa using h⟩, fun ⟨t, h⟩ => ⟨E t, by simp [h]⟩⟩)⟩

@[simp]

中文:
定义 ofEquiv
  签名: {f : 滤子 α} (F : f.实数izer) (E : F.σ ≃ τ)
  定义体: ⟨τ, F.F.ofEquiv E, by
    refine Eq.trans ?_ F.eq
    exact filter_eq (Set.ext fun _ =>
      ⟨fun ⟨s, h⟩ => ⟨E.symm s, by simpa using h⟩, fun ⟨t, h⟩ => ⟨E t, by simp [h]⟩⟩)⟩

@[simp]

Depends on / 依赖: E.symm, Eq.trans, F.F.ofEquiv, F.eq, Set.ext, filter_eq, ofEquiv
-/
def ofEquiv {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) : f.Realizer :=
  ⟨τ, F.F.ofEquiv E, by
    refine Eq.trans ?_ F.eq
    exact filter_eq (Set.ext fun _ =>
      ⟨fun ⟨s, h⟩ => ⟨E.symm s, by simpa using h⟩, fun ⟨t, h⟩ => ⟨E t, by simp [h]⟩⟩)⟩

@[simp]
/--
theorem `ofEquiv_σ` / 定理 `ofEquiv_σ`

English:
theorem ofEquiv_σ
  given: {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ)
  statement: (F.ofEquiv E).σ = τ
  proof: rfl

@[simp]

中文:
定理 ofEquiv_σ
  条件: {f : 滤子 α} (F : f.实数izer) (E : F.σ ≃ τ)
  结论: (F.ofEquiv E).σ = τ
  证明: rfl

@[simp]
-/
theorem ofEquiv_σ {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) : (F.ofEquiv E).σ = τ :=
  rfl

@[simp]
/--
theorem `ofEquiv_F` / 定理 `ofEquiv_F`

English:
theorem ofEquiv_F
  given: {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) (s : τ)
  proof: rfl

中文:
定理 ofEquiv_F
  条件: {f : 滤子 α} (F : f.实数izer) (E : F.σ ≃ τ) (s : τ)
  证明: rfl
-/
theorem ofEquiv_F {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) (s : τ) :
    (F.ofEquiv E).F s = F.F (E.symm s) := rfl

/--
Definition of `principal` / `principal` 的定义

English:
definition principal
  signature: (s : Set α)
  body: ⟨Unit,
    { f := fun _ => s
      pt := ()
      inf := fun _ _ => ()
      inf_le_left := fun _ _ => le_rfl
      inf_le_right := fun _ _ => le_rfl },
filter_eq Set.ext fun _ => ⟨fun ⟨_, s⟩ => s, fun h => ⟨(), h⟩⟩⟩

@[simp]

中文:
定义 principal
  签名: (s : 集合 α)
  定义体: ⟨Unit,
    { f := fun _ => s
      pt := ()
      inf := fun _ _ => ()
      inf_le_left := fun _ _ => le_rfl
      inf_le_right := fun _ _ => le_rfl },
filter_eq Set.ext fun _ => ⟨fun ⟨_, s⟩ => s, fun h => ⟨(), h⟩⟩⟩

@[simp]
-/
protected def principal (s : Set α) : (principal s).Realizer :=
  ⟨Unit,
    { f := fun _ => s
      pt := ()
      inf := fun _ _ => ()
      inf_le_left := fun _ _ => le_rfl
      inf_le_right := fun _ _ => le_rfl },
filter_eq Set.ext fun _ => ⟨fun ⟨_, s⟩ => s, fun h => ⟨(), h⟩⟩⟩

@[simp]
/--
theorem `principal_σ` / 定理 `principal_σ`

English:
theorem principal_σ
  given: (s : Set α)
  statement: (Realizer.principal s).σ = Unit
  proof: rfl

@[simp]

中文:
定理 principal_σ
  条件: (s : 集合 α)
  结论: (实数izer.principal s).σ = 单元
  证明: rfl

@[simp]
-/
theorem principal_σ (s : Set α) : (Realizer.principal s).σ = Unit :=
  rfl

@[simp]
/--
theorem `principal_F` / 定理 `principal_F`

English:
theorem principal_F
  given: (s : Set α) (u : Unit)
  statement: (Realizer.principal s).F u = s
  proof: rfl

中文:
定理 principal_F
  条件: (s : 集合 α) (u : 单元)
  结论: (实数izer.principal s).F u = s
  证明: rfl
-/
theorem principal_F (s : Set α) (u : Unit) : (Realizer.principal s).F u = s :=
  rfl

instance (s : Set α) : Inhabited (principal s).Realizer :=
  ⟨Realizer.principal s⟩

/--
Definition of `top` / `top` 的定义

English:
definition top
  signature: : (⊤ : Filter α).Realizer
  body: (Realizer.principal _).ofEq principal_univ

@[simp]

中文:
定义 top
  签名: : (⊤ : 滤子 α).实数izer
  定义体: (Realizer.principal _).ofEq principal_univ

@[simp]
-/
protected def top : (⊤ : Filter α).Realizer :=
  (Realizer.principal _).ofEq principal_univ

@[simp]
/--
theorem `top_σ` / 定理 `top_σ`

English:
theorem top_σ
  statement: (@Realizer.top α).σ = Unit
  proof: rfl

@[simp]

中文:
定理 top_σ
  结论: (@实数izer.top α).σ = 单元
  证明: rfl

@[simp]
-/
theorem top_σ : (@Realizer.top α).σ = Unit :=
  rfl

@[simp]
/--
theorem `top_F` / 定理 `top_F`

English:
theorem top_F
  given: (u : Unit)
  statement: (@Realizer.top α).F u = univ
  proof: rfl

中文:
定理 top_F
  条件: (u : 单元)
  结论: (@实数izer.top α).F u = univ
  证明: rfl
-/
theorem top_F (u : Unit) : (@Realizer.top α).F u = univ :=
  rfl

/--
Definition of `bot` / `bot` 的定义

English:
definition bot
  signature: : (⊥ : Filter α).Realizer
  body: (Realizer.principal _).ofEq principal_empty

@[simp]

中文:
定义 bot
  签名: : (⊥ : 滤子 α).实数izer
  定义体: (Realizer.principal _).ofEq principal_empty

@[simp]
-/
protected def bot : (⊥ : Filter α).Realizer :=
  (Realizer.principal _).ofEq principal_empty

@[simp]
/--
theorem `bot_σ` / 定理 `bot_σ`

English:
theorem bot_σ
  statement: (@Realizer.bot α).σ = Unit
  proof: rfl

@[simp]

中文:
定理 bot_σ
  结论: (@实数izer.bot α).σ = 单元
  证明: rfl

@[simp]

Depends on / 依赖: Nat.le_refl, _eq_none, getElem, le_refl
-/
theorem bot_σ : (@Realizer.bot α).σ = Unit :=
  rfl

@[simp]
/--
theorem `bot_F` / 定理 `bot_F`

English:
theorem bot_F
  given: (u : Unit)
  statement: (@Realizer.bot α).F u = ∅
  proof: rfl

中文:
定理 bot_F
  条件: (u : 单元)
  结论: (@实数izer.bot α).F u = ∅
  证明: rfl
-/
theorem bot_F (u : Unit) : (@Realizer.bot α).F u = ∅ :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (m : α -> β) {f : Filter α} (F : f.Realizer)
  body: ⟨F.σ,
    { f := fun s => image m (F.F s)
      pt := F.F.pt
      inf := F.F.inf
      inf_le_left := fun _ _ => image_mono (F.F.inf_le_left _ _)
      inf_le_right := fun _ _ => image_mono (F.F.inf_le_right _ _) },
filter_eq Set.ext fun _ => by
      simp only [CFilter.toFilter, image_subset_iff, mem_ofPred_eq, Filter.mem_sets, mem_map]
      rw [F.mem_sets]⟩

@[simp]

中文:
定义 map
  签名: (m : α -> β) {f : 滤子 α} (F : f.实数izer)
  定义体: ⟨F.σ,
    { f := fun s => image m (F.F s)
      pt := F.F.pt
      inf := F.F.inf
      inf_le_left := fun _ _ => image_mono (F.F.inf_le_left _ _)
      inf_le_right := fun _ _ => image_mono (F.F.inf_le_right _ _) },
filter_eq Set.ext fun _ => by
      simp only [CFilter.toFilter, image_subset_iff, mem_ofPred_eq, Filter.mem_sets, mem_map]
      rw [F.mem_sets]⟩

@[simp]
-/
protected def map (m : α -> β) {f : Filter α} (F : f.Realizer) : (map m f).Realizer :=
  ⟨F.σ,
    { f := fun s => image m (F.F s)
      pt := F.F.pt
      inf := F.F.inf
      inf_le_left := fun _ _ => image_mono (F.F.inf_le_left _ _)
      inf_le_right := fun _ _ => image_mono (F.F.inf_le_right _ _) },
filter_eq Set.ext fun _ => by
      simp only [CFilter.toFilter, image_subset_iff, mem_ofPred_eq, Filter.mem_sets, mem_map]
      rw [F.mem_sets]⟩

@[simp]
/--
theorem `map_σ` / 定理 `map_σ`

English:
theorem map_σ
  given: (m : α -> β) {f : Filter α} (F : f.Realizer)
  statement: (F.map m).σ = F.σ
  proof: rfl

@[simp]

中文:
定理 map_σ
  条件: (m : α -> β) {f : 滤子 α} (F : f.实数izer)
  结论: (F.map m).σ = F.σ
  证明: rfl

@[simp]
-/
theorem map_σ (m : α -> β) {f : Filter α} (F : f.Realizer) : (F.map m).σ = F.σ :=
  rfl

@[simp]
/--
theorem `map_F` / 定理 `map_F`

English:
theorem map_F
  given: (m : α -> β) {f : Filter α} (F : f.Realizer) (s)
  statement: (F.map m).F s = image m (F.F s)
  proof: rfl

中文:
定理 map_F
  条件: (m : α -> β) {f : 滤子 α} (F : f.实数izer) (s)
  结论: (F.map m).F s = 像 m (F.F s)
  证明: rfl
-/
theorem map_F (m : α -> β) {f : Filter α} (F : f.Realizer) (s) : (F.map m).F s = image m (F.F s) :=
  rfl

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (m : α -> β) {f : Filter β} (F : f.Realizer)
  body: ⟨F.σ,
    { f := fun s => preimage m (F.F s)
      pt := F.F.pt
      inf := F.F.inf
      inf_le_left := fun _ _ => preimage_mono (F.F.inf_le_left _ _)
      inf_le_right := fun _ _ => preimage_mono (F.F.inf_le_right _ _) },
filter_eq Set.ext fun _ => by
      cases F; subst f
      exact ⟨fun ⟨s, h⟩ => ⟨_, ⟨s, Subset.refl _⟩, h⟩,
        fun ⟨_, ⟨s, h⟩, h₂⟩ => ⟨s, Subset.trans (preimage_mono h) h₂⟩⟩⟩

中文:
定义 comap
  签名: (m : α -> β) {f : 滤子 β} (F : f.实数izer)
  定义体: ⟨F.σ,
    { f := fun s => preimage m (F.F s)
      pt := F.F.pt
      inf := F.F.inf
      inf_le_left := fun _ _ => preimage_mono (F.F.inf_le_left _ _)
      inf_le_right := fun _ _ => preimage_mono (F.F.inf_le_right _ _) },
filter_eq Set.ext fun _ => by
      cases F; subst f
      exact ⟨fun ⟨s, h⟩ => ⟨_, ⟨s, Subset.refl _⟩, h⟩,
        fun ⟨_, ⟨s, h⟩, h₂⟩ => ⟨s, Subset.trans (preimage_mono h) h₂⟩⟩⟩

Depends on / 依赖: ext_getElem
-/
protected def comap (m : α -> β) {f : Filter β} (F : f.Realizer) : (comap m f).Realizer :=
  ⟨F.σ,
    { f := fun s => preimage m (F.F s)
      pt := F.F.pt
      inf := F.F.inf
      inf_le_left := fun _ _ => preimage_mono (F.F.inf_le_left _ _)
      inf_le_right := fun _ _ => preimage_mono (F.F.inf_le_right _ _) },
filter_eq Set.ext fun _ => by
      cases F; subst f
      exact ⟨fun ⟨s, h⟩ => ⟨_, ⟨s, Subset.refl _⟩, h⟩,
        fun ⟨_, ⟨s, h⟩, h₂⟩ => ⟨s, Subset.trans (preimage_mono h) h₂⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sup` / `sup` 的定义

English:
definition sup
  signature: {f g : Filter α} (F : f.Realizer) (G : g.Realizer)
  body: ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.F s union G.F t
      pt := (F.F.pt, G.F.pt)
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.F.inf a b, G.F.inf a' b')
      inf_le_left := fun _ _ => union_subset_union (F.F.inf_le_left _ _) (G.F.inf_le_left _ _)
      inf_le_right := fun _ _ => union_subset_union (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
filter_eq Set.ext fun _ => by cases F; cases G; subst f g; simp [CFilter.toFilter]⟩

中文:
定义 上确界
  签名: {f g : 滤子 α} (F : f.实数izer) (G : g.实数izer)
  定义体: ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.F s union G.F t
      pt := (F.F.pt, G.F.pt)
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.F.inf a b, G.F.inf a' b')
      inf_le_left := fun _ _ => union_subset_union (F.F.inf_le_left _ _) (G.F.inf_le_left _ _)
      inf_le_right := fun _ _ => union_subset_union (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
filter_eq Set.ext fun _ => by cases F; cases G; subst f g; simp [CFilter.toFilter]⟩

Depends on / 依赖: _pos, ext_getElem, getElem
-/
protected def sup {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : (f ⊔ g).Realizer :=
  ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.F s union G.F t
      pt := (F.F.pt, G.F.pt)
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.F.inf a b, G.F.inf a' b')
      inf_le_left := fun _ _ => union_subset_union (F.F.inf_le_left _ _) (G.F.inf_le_left _ _)
      inf_le_right := fun _ _ => union_subset_union (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
filter_eq Set.ext fun _ => by cases F; cases G; subst f g; simp [CFilter.toFilter]⟩

/--
Definition of `inf` / `inf` 的定义

English:
definition inf
  signature: {f g : Filter α} (F : f.Realizer) (G : g.Realizer)
  body: ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.F s inter G.F t
      pt := (F.F.pt, G.F.pt)
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.F.inf a b, G.F.inf a' b')
      inf_le_left := fun _ _ => inter_subset_inter (F.F.inf_le_left _ _) (G.F.inf_le_left _ _)
      inf_le_right := fun _ _ => inter_subset_inter (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
    by
      cases F; cases G; subst f g; simp only [CFilter.toFilter, Prod.exists]; ext
      constructor
      · rintro ⟨s, t, h⟩
        apply mem_inf_of_inter _ _ h
        · use s
        · use t
      · rintro ⟨_, ⟨a, ha⟩, _, ⟨b, hb⟩, rfl⟩
        exact ⟨a, b, inter_subset_inter ha hb⟩⟩

中文:
定义 下确界
  签名: {f g : 滤子 α} (F : f.实数izer) (G : g.实数izer)
  定义体: ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.F s inter G.F t
      pt := (F.F.pt, G.F.pt)
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.F.inf a b, G.F.inf a' b')
      inf_le_left := fun _ _ => inter_subset_inter (F.F.inf_le_left _ _) (G.F.inf_le_left _ _)
      inf_le_right := fun _ _ => inter_subset_inter (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
    by
      cases F; cases G; subst f g; simp only [CFilter.toFilter, Prod.exists]; ext
      constructor
      · rintro ⟨s, t, h⟩
        apply mem_inf_of_inter _ _ h
        · use s
        · use t
      · rintro ⟨_, ⟨a, ha⟩, _, ⟨b, hb⟩, rfl⟩
        exact ⟨a, b, inter_subset_inter ha hb⟩⟩
-/
protected def inf {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : (f ⊓ g).Realizer :=
  ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.F s inter G.F t
      pt := (F.F.pt, G.F.pt)
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.F.inf a b, G.F.inf a' b')
      inf_le_left := fun _ _ => inter_subset_inter (F.F.inf_le_left _ _) (G.F.inf_le_left _ _)
      inf_le_right := fun _ _ => inter_subset_inter (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
    by
      cases F; cases G; subst f g; simp only [CFilter.toFilter, Prod.exists]; ext
      constructor
      · rintro ⟨s, t, h⟩
        apply mem_inf_of_inter _ _ h
        · use s
        · use t
      · rintro ⟨_, ⟨a, ha⟩, _, ⟨b, hb⟩, rfl⟩
        exact ⟨a, b, inter_subset_inter ha hb⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cofinite` / `cofinite` 的定义

English:
definition cofinite
  signature: [DecidableEq α]
  body: ⟨Finset α,
    { f := fun s => { a | a ∉ s }
      pt := ∅
      inf := (· union ·)
      inf_le_left := fun _ _ _ => mt (Finset.mem_union_left _)
      inf_le_right := fun _ _ _ => mt (Finset.mem_union_right _) },
filter_eq
      Set.ext fun _ =>
        ⟨fun ⟨s, h⟩ => s.finite_toSet.subset (compl_subset_comm.1 h), fun h =>
          ⟨h.toFinset, by simp⟩⟩⟩

中文:
定义 cofinite
  签名: [DecidableEq α]
  定义体: ⟨Finset α,
    { f := fun s => { a | a ∉ s }
      pt := ∅
      inf := (· union ·)
      inf_le_left := fun _ _ _ => mt (Finset.mem_union_left _)
      inf_le_right := fun _ _ _ => mt (Finset.mem_union_right _) },
filter_eq
      Set.ext fun _ =>
        ⟨fun ⟨s, h⟩ => s.finite_toSet.subset (compl_subset_comm.1 h), fun h =>
          ⟨h.toFinset, by simp⟩⟩⟩

Depends on / 依赖: _eq_getElem, getElem, getElem_idxOf, idxOf_lt_length_iff
-/
protected def cofinite [DecidableEq α] : (@cofinite α).Realizer :=
  ⟨Finset α,
    { f := fun s => { a | a ∉ s }
      pt := ∅
      inf := (· union ·)
      inf_le_left := fun _ _ _ => mt (Finset.mem_union_left _)
      inf_le_right := fun _ _ _ => mt (Finset.mem_union_right _) },
filter_eq
      Set.ext fun _ =>
        ⟨fun ⟨s, h⟩ => s.finite_toSet.subset (compl_subset_comm.1 h), fun h =>
          ⟨h.toFinset, by simp⟩⟩⟩

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: {f : Filter α} {m : α -> Filter β} (F : f.Realizer) (G : forall i, (m i).Realizer)
  body: ⟨Σ s : F.σ, forall i in F.F s, (G i).σ,
    { f := fun ⟨s, f⟩ => ⋃ i in F.F s, (G i).F (f i (by assumption))
      pt := ⟨F.F.pt, fun i _ => (G i).F.pt⟩
      inf := fun ⟨a, f⟩ ⟨b, f'⟩ =>
        ⟨F.F.inf a b, fun i h =>
          (G i).F.inf (f i (F.F.inf_le_left _ _ h)) (f' i (F.F.inf_le_right _ _ h))⟩
      inf_le_left := fun _ _ _ => by
        simp only [mem_iUnion, forall_exists_index]
        exact fun i h₁ h₂ => ⟨i, F.F.inf_le_left _ _ h₁, (G i).F.inf_le_left _ _ h₂⟩
      inf_le_right := fun _ _ _ => by
        simp only [mem_iUnion, forall_exists_index]
        exact fun i h₁ h₂ => ⟨i, F.F.inf_le_right _ _ h₁, (G i).F.inf_le_right _ _ h₂⟩ },
filter_eq Set.ext fun _ => by
      obtain ⟨_, F, _⟩ := F; subst f
      simp only [CFilter.toFilter, iUnion_subset_iff, Sigma.exists, Filter.mem_sets, mem_bind]
      exact
        ⟨fun ⟨s, f, h⟩ =>
          ⟨F s, ⟨s, Subset.refl _⟩, fun i H => (G i).mem_sets.2 ⟨f i H, fun _ h' => h i H h'⟩⟩,
          fun ⟨_, ⟨s, h⟩, f⟩ =>
          let ⟨f', h'⟩ := Classical.axiom_of_choice fun i : F s => (G i).mem_sets.1 (f i (h i.2))
          ⟨s, fun i h => f' ⟨i, h⟩, fun _ H _ m => h' ⟨_, H⟩ m⟩⟩⟩

中文:
定义 bind
  签名: {f : 滤子 α} {m : α -> 滤子 β} (F : f.实数izer) (G : 对任意 i, (m i).实数izer)
  定义体: ⟨Σ s : F.σ, forall i in F.F s, (G i).σ,
    { f := fun ⟨s, f⟩ => ⋃ i in F.F s, (G i).F (f i (by assumption))
      pt := ⟨F.F.pt, fun i _ => (G i).F.pt⟩
      inf := fun ⟨a, f⟩ ⟨b, f'⟩ =>
        ⟨F.F.inf a b, fun i h =>
          (G i).F.inf (f i (F.F.inf_le_left _ _ h)) (f' i (F.F.inf_le_right _ _ h))⟩
      inf_le_left := fun _ _ _ => by
        simp only [mem_iUnion, forall_exists_index]
        exact fun i h₁ h₂ => ⟨i, F.F.inf_le_left _ _ h₁, (G i).F.inf_le_left _ _ h₂⟩
      inf_le_right := fun _ _ _ => by
        simp only [mem_iUnion, forall_exists_index]
        exact fun i h₁ h₂ => ⟨i, F.F.inf_le_right _ _ h₁, (G i).F.inf_le_right _ _ h₂⟩ },
filter_eq Set.ext fun _ => by
      obtain ⟨_, F, _⟩ := F; subst f
      simp only [CFilter.toFilter, iUnion_subset_iff, Sigma.exists, Filter.mem_sets, mem_bind]
      exact
        ⟨fun ⟨s, f, h⟩ =>
          ⟨F s, ⟨s, Subset.refl _⟩, fun i H => (G i).mem_sets.2 ⟨f i H, fun _ h' => h i H h'⟩⟩,
          fun ⟨_, ⟨s, h⟩, f⟩ =>
          let ⟨f', h'⟩ := Classical.axiom_of_choice fun i : F s => (G i).mem_sets.1 (f i (h i.2))
          ⟨s, fun i h => f' ⟨i, h⟩, fun _ H _ m => h' ⟨_, H⟩ m⟩⟩⟩
-/
protected def bind {f : Filter α} {m : α -> Filter β} (F : f.Realizer) (G : forall i, (m i).Realizer) :
    (f.bind m).Realizer :=
  ⟨Σ s : F.σ, forall i in F.F s, (G i).σ,
    { f := fun ⟨s, f⟩ => ⋃ i in F.F s, (G i).F (f i (by assumption))
      pt := ⟨F.F.pt, fun i _ => (G i).F.pt⟩
      inf := fun ⟨a, f⟩ ⟨b, f'⟩ =>
        ⟨F.F.inf a b, fun i h =>
          (G i).F.inf (f i (F.F.inf_le_left _ _ h)) (f' i (F.F.inf_le_right _ _ h))⟩
      inf_le_left := fun _ _ _ => by
        simp only [mem_iUnion, forall_exists_index]
        exact fun i h₁ h₂ => ⟨i, F.F.inf_le_left _ _ h₁, (G i).F.inf_le_left _ _ h₂⟩
      inf_le_right := fun _ _ _ => by
        simp only [mem_iUnion, forall_exists_index]
        exact fun i h₁ h₂ => ⟨i, F.F.inf_le_right _ _ h₁, (G i).F.inf_le_right _ _ h₂⟩ },
filter_eq Set.ext fun _ => by
      obtain ⟨_, F, _⟩ := F; subst f
      simp only [CFilter.toFilter, iUnion_subset_iff, Sigma.exists, Filter.mem_sets, mem_bind]
      exact
        ⟨fun ⟨s, f, h⟩ =>
          ⟨F s, ⟨s, Subset.refl _⟩, fun i H => (G i).mem_sets.2 ⟨f i H, fun _ h' => h i H h'⟩⟩,
          fun ⟨_, ⟨s, h⟩, f⟩ =>
          let ⟨f', h'⟩ := Classical.axiom_of_choice fun i : F s => (G i).mem_sets.1 (f i (h i.2))
          ⟨s, fun i h => f' ⟨i, h⟩, fun _ H _ m => h' ⟨_, H⟩ m⟩⟩⟩

/--
Definition of `iSup` / `iSup` 的定义

English:
definition iSup
  signature: {f : α -> Filter β} (F : forall i, (f i).Realizer)
  body: let F' : (⨆ i, f i).Realizer :=
(Realizer.bind Realizer.top F).ofEq
filter_eq Set.ext by simp [Filter.bind, iSup_sets_eq]
F'.ofEquiv
    show (Σ _ : Unit, forall i : α, True -> (F i).σ) ≃ forall i, (F i).σ from
      ⟨fun ⟨_, f⟩ i => f i ⟨⟩, fun f => ⟨(), fun i _ => f i⟩, fun _ => rfl, fun _ => rfl⟩

中文:
定义 iSup
  签名: {f : α -> 滤子 β} (F : 对任意 i, (f i).实数izer)
  定义体: let F' : (⨆ i, f i).Realizer :=
(Realizer.bind Realizer.top F).ofEq
filter_eq Set.ext by simp [Filter.bind, iSup_sets_eq]
F'.ofEquiv
    show (Σ _ : Unit, forall i : α, True -> (F i).σ) ≃ forall i, (F i).σ from
      ⟨fun ⟨_, f⟩ i => f i ⟨⟩, fun f => ⟨(), fun i _ => f i⟩, fun _ => rfl, fun _ => rfl⟩
-/
protected def iSup {f : α -> Filter β} (F : forall i, (f i).Realizer) : (⨆ i, f i).Realizer :=
  let F' : (⨆ i, f i).Realizer :=
(Realizer.bind Realizer.top F).ofEq
filter_eq Set.ext by simp [Filter.bind, iSup_sets_eq]
F'.ofEquiv
    show (Σ _ : Unit, forall i : α, True -> (F i).σ) ≃ forall i, (F i).σ from
      ⟨fun ⟨_, f⟩ i => f i ⟨⟩, fun f => ⟨(), fun i _ => f i⟩, fun _ => rfl, fun _ => rfl⟩

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {f g : Filter α} (F : f.Realizer) (G : g.Realizer)
  body: (F.comap _).inf (G.comap _)

中文:
定义 乘积
  签名: {f g : 滤子 α} (F : f.实数izer) (G : g.实数izer)
  定义体: (F.comap _).inf (G.comap _)
-/
protected def prod {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : (f ×ˢ g).Realizer :=
  (F.comap _).inf (G.comap _)

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  given: {f g : Filter α} (F : f.Realizer) (G : g.Realizer)
  proof: ⟨fun H t => F.mem_sets.1 (H (G.mem_sets.2 ⟨t, Subset.refl _⟩)), fun H _ h =>
F.mem_sets.2
      let ⟨s, h₁⟩ := G.mem_sets.1 h
      let ⟨t, h₂⟩ := H s
      ⟨t, Subset.trans h₂ h₁⟩⟩

中文:
定理 le_iff
  条件: {f g : 滤子 α} (F : f.实数izer) (G : g.实数izer)
  证明: ⟨fun H t => F.mem_sets.1 (H (G.mem_sets.2 ⟨t, Subset.refl _⟩)), fun H _ h =>
F.mem_sets.2
      let ⟨s, h₁⟩ := G.mem_sets.1 h
      let ⟨t, h₂⟩ := H s
      ⟨t, Subset.trans h₂ h₁⟩⟩

Depends on / 依赖: F.mem_sets, G.mem_sets, Subset, Subset.refl, Subset.trans, mem_sets
-/
theorem le_iff {f g : Filter α} (F : f.Realizer) (G : g.Realizer) :
    f <= g ↔ forall b : G.σ, exists a : F.σ, F.F a <= G.F b :=
  ⟨fun H t => F.mem_sets.1 (H (G.mem_sets.2 ⟨t, Subset.refl _⟩)), fun H _ h =>
F.mem_sets.2
      let ⟨s, h₁⟩ := G.mem_sets.1 h
      let ⟨t, h₂⟩ := H s
      ⟨t, Subset.trans h₂ h₁⟩⟩

/--
theorem `tendsto_iff` / 定理 `tendsto_iff`

English:
theorem tendsto_iff
  statement: (f : α -> β) {l₁ : Filter α} {l₂ : Filter β} (L₁ : l₁.Realizer)
  proof: (le_iff (L₁.map f) L₂).trans forall_congr' fun _ => exists_congr fun _ => image_subset_iff

中文:
定理 tendsto_iff
  结论: (f : α -> β) {l₁ : 滤子 α} {l₂ : 滤子 β} (L₁ : l₁.实数izer)
  证明: (le_iff (L₁.map f) L₂).trans forall_congr' fun _ => exists_congr fun _ => image_subset_iff

Depends on / 依赖: exists_congr, forall_congr, image_subset_iff, le_iff
-/
theorem tendsto_iff (f : α -> β) {l₁ : Filter α} {l₂ : Filter β} (L₁ : l₁.Realizer)
    (L₂ : l₂.Realizer) : Tendsto f l₁ l₂ ↔ forall b, exists a, forall x in L₁.F a, f x in L₂.F b :=
(le_iff (L₁.map f) L₂).trans forall_congr' fun _ => exists_congr fun _ => image_subset_iff

/--
theorem `ne_bot_iff` / 定理 `ne_bot_iff`

English:
theorem ne_bot_iff
  given: {f : Filter α} (F : f.Realizer)
  statement: f != ⊥ ↔ forall a : F.σ, (F.F a).Nonempty
  proof: by
  rw [not_iff_comm]; rw [← le_bot_iff]; rw [F.le_iff Realizer.bot]; rw [not_forall]
  simp only [Set.not_nonempty_iff_eq_empty]
  exact ⟨fun ⟨x, e⟩ _ => ⟨x, le_of_eq e⟩, fun h =>
    let ⟨x, h⟩ := h ()
    ⟨x, le_bot_iff.1 h⟩⟩

中文:
定理 ne_bot_iff
  条件: {f : 滤子 α} (F : f.实数izer)
  结论: f != ⊥ ↔ 对任意 a : F.σ, (F.F a).非空
  证明: by
  rw [not_iff_comm]; rw [← le_bot_iff]; rw [F.le_iff Realizer.bot]; rw [not_forall]
  simp only [Set.not_nonempty_iff_eq_empty]
  exact ⟨fun ⟨x, e⟩ _ => ⟨x, le_of_eq e⟩, fun h =>
    let ⟨x, h⟩ := h ()
    ⟨x, le_bot_iff.1 h⟩⟩

Depends on / 依赖: F.le_iff, Realizer, Realizer.bot, Set.not_nonempty_iff_eq_empty, le_bot_iff, le_iff, le_of_eq, not_forall, not_iff_comm, not_nonempty_iff_eq_empty
-/
theorem ne_bot_iff {f : Filter α} (F : f.Realizer) : f != ⊥ ↔ forall a : F.σ, (F.F a).Nonempty := by
  rw [not_iff_comm]; rw [← le_bot_iff]; rw [F.le_iff Realizer.bot]; rw [not_forall]
  simp only [Set.not_nonempty_iff_eq_empty]
  exact ⟨fun ⟨x, e⟩ _ => ⟨x, le_of_eq e⟩, fun h =>
    let ⟨x, h⟩ := h ()
    ⟨x, le_bot_iff.1 h⟩⟩

end Filter.Realizer
