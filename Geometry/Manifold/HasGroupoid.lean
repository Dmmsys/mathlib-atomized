/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Charted spaces with a given structure groupoid
-/

@[expose] public section

noncomputable section

open TopologicalSpace Topology

universe u

variable {H : Type u} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}

open Set OpenPartialHomeomorph Manifold

section HasGroupoid

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-- A charted space has an atlas in a groupoid `G` if the change of coordinates belong to the
groupoid. -/
/-
**HasGroupoid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{H : Type u_5} →   [inst : TopologicalSpace H] →     (M : Type u_6) → [ins
t_1 : TopologicalSpace M] → [ChartedSpace H M] → StructureGroupoid H → Prop
参数：M : Type u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A charted space has an atlas in a groupoid `G` if the change of coordinates belo
ng to the
groupoid.
-/
class HasGroupoid {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (G : StructureGroupoid H) : Prop where
  compatible :
    ∀ {e e' : OpenPartialHomeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M → e.symm ≫ₕ e' ∈ G

/-- Reformulate in the `StructureGroupoid` namespace the compatibility condition of charts in a
charted space admitting a structure groupoid, to make it more easily accessible with dot
notation. -/
/-
**StructureGroupoid.compatible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StructureGroupoid.compatible {H : Type*} [TopologicalSpace H] (G : Structu
reGroupoid H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M
 G] {e e' : OpenPartialHomeomorph M H} (he : e in atlas H M) (he' : e' in atlas 
H M) : e.symm ≫ₕ e' in G
参数：G : StructureGroupoid H；he : e in atlas H M；he' : e' in atlas H M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGroupoid.compatible`：∀ {H : Type u_5} {inst : TopologicalSpace H} {M 
: Type u_6} {inst_1 : TopologicalSpace M} {inst_2 : ChartedSpace H M}   {G : Str
uctureGroupo…

--- 原说明 ---
Reformulate in the `StructureGroupoid` namespace the compatibility condition of 
charts in a
charted space admitting a structure groupoid, to make it more easily accessible 
with dot
notation.
-/
theorem StructureGroupoid.compatible {H : Type*} [TopologicalSpace H] (G : StructureGroupoid H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G]
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) :
    e.symm ≫ₕ e' ∈ G :=
  HasGroupoid.compatible he he'
/-
**hasGroupoid_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGroupoid_of_le {G₁ G₂ : StructureGroupoid H} (h : HasGroupoid M G₁) (hl
e : G₁ <= G₂) : HasGroupoid M G₂
参数：h : HasGroupoid M G₁；hle : G₁ <= G₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasGroupoid.compatible`：∀ {H : Type u_5} {inst : TopologicalSpace H} {M 
: Type u_6} {inst_1 : TopologicalSpace M} {inst_2 : ChartedSpace H M}   {G : Str
uctureGroupo…
-/
theorem hasGroupoid_of_le {G₁ G₂ : StructureGroupoid H} (h : HasGroupoid M G₁) (hle : G₁ ≤ G₂) :
    HasGroupoid M G₂ :=
  ⟨fun he he' ↦ hle (h.compatible he he')⟩
/-
**hasGroupoid_inf_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGroupoid_inf_iff {G₁ G₂ : StructureGroupoid H} : HasGroupoid M (G₁ ⊓ G₂
) ↔ HasGroupoid M G₁ ∧ HasGroupoid M G₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasGroupoid_of_le`：hasGroupoid_of_le {G₁ G₂ : StructureGroupoid H} (h : 
HasGroupoid M G₁) (hle : G₁ <= G₂) : HasGroupoid M G₂
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `HasGroupoid.compatible`：∀ {H : Type u_5} {inst : TopologicalSpace H} {M 
: Type u_6} {inst_1 : TopologicalSpace M} {inst_2 : ChartedSpace H M}   {G : Str
uctureGroupo…
-/
theorem hasGroupoid_inf_iff {G₁ G₂ : StructureGroupoid H} : HasGroupoid M (G₁ ⊓ G₂) ↔
    HasGroupoid M G₁ ∧ HasGroupoid M G₂ :=
  ⟨(fun h ↦ ⟨hasGroupoid_of_le h inf_le_left, hasGroupoid_of_le h inf_le_right⟩),
  fun ⟨h1, h2⟩ ↦ { compatible := fun he he' ↦ ⟨h1.compatible he he', h2.compatible he he'⟩ }⟩
/-
**hasGroupoid_of_pregroupoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasGroupoid_of_pregroupoid (PG : Pregroupoid H) (h : forall {e e' : OpenPa
rtialHomeomorph M H}, e in atlas H M -> e' in atlas H M -> PG.property (e.symm ≫
ₕ e') (e.symm ≫ₕ e').source) : HasGroupoid M PG.groupoid
参数：PG : Pregroupoid H；h : forall {e e' : OpenPartialHomeomorph M H}, e in atlas 
H M -> e' in atlas H M -> PG.property (e.symm ≫ₕ e') (e.symm ≫ₕ e').source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_groupoid_of_pregroupoid`：mem_groupoid_of_pregroupoid {PG : Pregroupo
id H} {e : OpenPartialHomeomorph H H} : e in PG.groupoid ↔ PG.property e e.sourc
e ∧ PG.property e…
-/
theorem hasGroupoid_of_pregroupoid (PG : Pregroupoid H) (h : ∀ {e e' : OpenPartialHomeomorph M H},
    e ∈ atlas H M → e' ∈ atlas H M → PG.property (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    HasGroupoid M PG.groupoid :=
  ⟨fun he he' ↦ mem_groupoid_of_pregroupoid.mpr ⟨h he he', h he' he⟩⟩

/-- The trivial charted space structure on the model space is compatible with any groupoid. -/
/-
**hasGroupoid_model_space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：hasGroupoid_model_space (H : Type*) [TopologicalSpace H] (G : StructureGro
upoid H) : HasGroupoid H G where compatible {e e'} he he'
参数：H : Type*；G : StructureGroupoid H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `chartedSpaceSelf_atlas`：chartedSpaceSelf_atlas {H : Type*} [TopologicalS
pace H] {e : OpenPartialHomeomorph H H} : e in atlas H H ↔ e = OpenPartialHomeom
orph.refl H
· 使用定理 `OpenPartialHomeomorph.trans_refl`：trans_refl : e.trans (OpenPartialHomeo
morph.refl Y) = e

--- 原说明 ---
The trivial charted space structure on the model space is compatible with any gr
oupoid.
-/
instance hasGroupoid_model_space (H : Type*) [TopologicalSpace H] (G : StructureGroupoid H) :
    HasGroupoid H G where
  compatible {e e'} he he' := by
    rw [chartedSpaceSelf_atlas] at he he'
    simp [he, he', StructureGroupoid.id_mem]

/-- Any charted space structure is compatible with the groupoid of all open partial
homeomorphisms. -/
/-
**hasGroupoid_continuousGroupoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：hasGroupoid_continuousGroupoid : HasGroupoid M (continuousGroupoid H)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousGroupoid.eq_1`：∀ (H : Type u_2) [inst : TopologicalSpace H], c
ontinuousGroupoid H = (continuousPregroupoid H).groupoid
· 使用定理 `mem_groupoid_of_pregroupoid`：mem_groupoid_of_pregroupoid {PG : Pregroupo
id H} {e : OpenPartialHomeomorph H H} : e in PG.groupoid ↔ PG.property e e.sourc
e ∧ PG.property e…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Any charted space structure is compatible with the groupoid of all open partial
homeomorphisms.
-/
instance hasGroupoid_continuousGroupoid : HasGroupoid M (continuousGroupoid H) := by
  refine ⟨fun _ _ ↦ ?_⟩
  rw [continuousGroupoid, mem_groupoid_of_pregroupoid]
  simp only [and_self_iff]

/-- If `G` is closed under restriction, the transition function between the restriction of two
charts `e` and `e'` lies in `G`. -/
/-
**StructureGroupoid.trans_restricted** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StructureGroupoid.trans_restricted {e e' : OpenPartialHomeomorph M H} {G :
 StructureGroupoid H} (he : e in atlas H M) (he' : e' in atlas H M) [HasGroupoid
 M G] [ClosedUnderRestriction G] {s : Opens M} (hs : Nonempty s) : (e.subtypeRes
tr hs).symm ≫ₕ e'.subtypeRestr hs in G
参数：he : e in atlas H M；he' : e' in atlas H M；hs : Nonempty s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.mem_of_eqOnSource`：StructureGroupoid.mem_of_eqOnSource
 (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (h :
 e' ≈ e) : e' in G
· 使用定理 `closedUnderRestriction'`：closedUnderRestriction' {G : StructureGroupoid 
H} [ClosedUnderRestriction G] {e : OpenPartialHomeomorph H H} (he : e in G) {s :
 Set H} (hs :…
· 使用定理 `StructureGroupoid.compatible`：StructureGroupoid.compatible {H : Type*} [
TopologicalSpace H] (G : StructureGroupoid H) {M : Type*} [TopologicalSpace M] [
ChartedSpace H M] …
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage_symm`：isOpen_inter_preimage_
symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target inter e.symm ⁻¹' s)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr`：subtypeRestr
_symm_trans_subtypeRestr (f f' : OpenPartialHomeomorph X Y) : (f.subtypeRestr hs
).symm.trans (f'.subtypeRestr hs) ≈ (f.symm.tran…

--- 原说明 ---
If `G` is closed under restriction, the transition function between the restrict
ion of two
charts `e` and `e'` lies in `G`.
-/
theorem StructureGroupoid.trans_restricted {e e' : OpenPartialHomeomorph M H}
    {G : StructureGroupoid H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M)
    [HasGroupoid M G] [ClosedUnderRestriction G] {s : Opens M} (hs : Nonempty s) :
    (e.subtypeRestr hs).symm ≫ₕ e'.subtypeRestr hs ∈ G :=
  G.mem_of_eqOnSource (closedUnderRestriction' (G.compatible he he')
    (e.isOpen_inter_preimage_symm s.2)) (e.subtypeRestr_symm_trans_subtypeRestr hs e')

section MaximalAtlas

variable (G : StructureGroupoid H)

variable (M) in
/-- Given a charted space admitting a structure groupoid, the maximal atlas associated to this
structure groupoid is the set of all charts that are compatible with the atlas, i.e., such
that changing coordinates with an atlas member gives an element of the groupoid. -/
/-
**StructureGroupoid.maximalAtlas** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StructureGroupoid.maximalAtlas : Set (OpenPartialHomeomorph M H)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a charted space admitting a structure groupoid, the maximal atlas associat
ed to this
structure groupoid is the set of all charts that are compatible with the atlas, 
i.e., such
that changing coordinates with an atlas member gives an element of the groupoid.
-/
def StructureGroupoid.maximalAtlas : Set (OpenPartialHomeomorph M H) :=
  { e | ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G }

/-- The elements of the atlas belong to the maximal atlas for any structure groupoid. -/
/-
**StructureGroupoid.subset_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StructureGroupoid.subset_maximalAtlas [HasGroupoid M G] : atlas H M subset
eq G.maximalAtlas M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.compatible`：StructureGroupoid.compatible {H : Type*} [
TopologicalSpace H] (G : StructureGroupoid H) {M : Type*} [TopologicalSpace M] [
ChartedSpace H M] …

--- 原说明 ---
The elements of the atlas belong to the maximal atlas for any structure groupoid
.
-/
theorem StructureGroupoid.subset_maximalAtlas [HasGroupoid M G] : atlas H M ⊆ G.maximalAtlas M :=
  fun _ he _ he' ↦ ⟨G.compatible he he', G.compatible he' he⟩
/-
**StructureGroupoid.chart_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StructureGroupoid.chart_mem_maximalAtlas [HasGroupoid M G] (x : M) : chart
At H x in G.maximalAtlas M
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.subset_maximalAtlas`：StructureGroupoid.subset_maximalA
tlas [HasGroupoid M G] : atlas H M subseteq G.maximalAtlas M
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M
-/
theorem StructureGroupoid.chart_mem_maximalAtlas [HasGroupoid M G] (x : M) :
    chartAt H x ∈ G.maximalAtlas M :=
  G.subset_maximalAtlas (chart_mem_atlas H x)

variable {G}
/-
**mem_maximalAtlas_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_maximalAtlas_iff {e : OpenPartialHomeomorph M H} : e in G.maximalAtlas
 M ↔ forall e' in atlas H M, e.symm ≫ₕ e' in G ∧ e'.symm ≫ₕ e in G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_maximalAtlas_iff {e : OpenPartialHomeomorph M H} :
    e ∈ G.maximalAtlas M ↔ ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G :=
  Iff.rfl
/-
**StructureGroupoid.compatible_of_mem_maximalAtlas_right** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：StructureGroupoid.compatible_of_mem_maximalAtlas_right {e' : OpenPartialHo
meomorph M H} {x : M} (he' : e' in G.maximalAtlas M) : (chartAt H x).symm ≫ₕ e' 
in G
参数：he' : e' in G.maximalAtlas M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ChartedSpace.chart_mem_atlas`：∀ {H : Type u_5} {inst : TopologicalSpace 
H} {M : Type u_6} {inst_1 : TopologicalSpace M} [self : ChartedSpace H M]   (x :
 M), ChartedSpace.…
-/
theorem StructureGroupoid.compatible_of_mem_maximalAtlas_right
    {e' : OpenPartialHomeomorph M H} {x : M}
    (he' : e' ∈ G.maximalAtlas M) : (chartAt H x).symm ≫ₕ e' ∈ G :=
  (he' _ (ChartedSpace.chart_mem_atlas x)).2
/-
**StructureGroupoid.compatible_of_mem_maximalAtlas_left** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：StructureGroupoid.compatible_of_mem_maximalAtlas_left {e' : OpenPartialHom
eomorph M H} {x : M} (he' : e' in G.maximalAtlas M) : e'.symm ≫ₕ chartAt H x in 
G
参数：he' : e' in G.maximalAtlas M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ChartedSpace.chart_mem_atlas`：∀ {H : Type u_5} {inst : TopologicalSpace 
H} {M : Type u_6} {inst_1 : TopologicalSpace M} [self : ChartedSpace H M]   (x :
 M), ChartedSpace.…
-/
theorem StructureGroupoid.compatible_of_mem_maximalAtlas_left
    {e' : OpenPartialHomeomorph M H} {x : M}
    (he' : e' ∈ G.maximalAtlas M) : e'.symm ≫ₕ chartAt H x ∈ G :=
  (he' _ (ChartedSpace.chart_mem_atlas x)).1

/-- Changing coordinates between two elements of the maximal atlas gives rise to an element
of the structure groupoid. -/
/-
**StructureGroupoid.compatible_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StructureGroupoid.compatible_of_mem_maximalAtlas {e e' : OpenPartialHomeom
orph M H} (he : e in G.maximalAtlas M) (he' : e' in G.maximalAtlas M) : e.symm ≫
ₕ e' in G
参数：he : e in G.maximalAtlas M；he' : e' in G.maximalAtlas M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.locality`：StructureGroupoid.locality (G : StructureGro
upoid H) {e : OpenPartialHomeomorph H H} (h : forall x in e.source, exists s, Is
Open s ∧ x in s …
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `mem_maximalAtlas_iff`：mem_maximalAtlas_iff {e : OpenPartialHomeomorph M 
H} : e in G.maximalAtlas M ↔ forall e' in atlas H M, e.symm ≫ₕ e' in G ∧ e'.symm
 ≫ₕ e in G
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `StructureGroupoid.trans`：StructureGroupoid.trans (G : StructureGroupoid 
H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (he' : e' in G) : e ≫ₕ e' in
 G
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.trans_assoc`：trans_assoc (e'' : OpenPartialHomeomo
rph Z Z') : (e.trans e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OpenPartialHomeomorph.EqOnSource.trans'`：∀ {X : Type u_1} {Y : Type u_3}
 {Z : Type u_5} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [ins
t_2 : TopologicalSpace Z] {e …
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `OpenPartialHomeomorph.self_trans_symm`：self_trans_symm : e.trans e.symm 
≈ OpenPartialHomeomorph.ofSet e.source e.open_source
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用定理 `OpenPartialHomeomorph.trans_of_set'`：trans_of_set' {s : Set Y} (hs : IsO
pen s) : e.trans (ofSet s hs) = e.restr (e.source inter e ⁻¹' s)
· 使用定理 `OpenPartialHomeomorph.restr_trans`：restr_trans (s : Set X) : (e.restr s)
.trans e' = (e.trans e').restr s
· 使用定理 `StructureGroupoid.mem_of_eqOnSource`：StructureGroupoid.mem_of_eqOnSource
 (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (h :
 e' ≈ e) : e' in G
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a

--- 原说明 ---
Changing coordinates between two elements of the maximal atlas gives rise to an 
element
of the structure groupoid.
-/
theorem StructureGroupoid.compatible_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ G.maximalAtlas M) (he' : e' ∈ G.maximalAtlas M) : e.symm ≫ₕ e' ∈ G := by
  refine G.locality fun x hx ↦ ?_
  set f := chartAt (H := H) (e.symm x)
  let s := e.target ∩ e.symm ⁻¹' f.source
  have hs : IsOpen s := by
    apply e.symm.continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
  have xs : x ∈ s := by
    simp only [s, f, mem_inter_iff, mem_preimage, mem_chart_source, and_true]
    exact ((mem_inter_iff _ _ _).1 hx).1
  refine ⟨s, hs, xs, ?_⟩
  have A : e.symm ≫ₕ f ∈ G := (mem_maximalAtlas_iff.1 he f (chart_mem_atlas _ _)).1
  have B : f.symm ≫ₕ e' ∈ G := (mem_maximalAtlas_iff.1 he' f (chart_mem_atlas _ _)).2
  have C : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ∈ G := G.trans A B
  have D : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ≈ (e.symm ≫ₕ e').restr s := calc
    (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' := by simp only [trans_assoc]
    _ ≈ e.symm ≫ₕ ofSet f.source f.open_source ≫ₕ e' :=
      EqOnSource.trans' (refl _) (EqOnSource.trans' (self_trans_symm _) (refl _))
    _ ≈ (e.symm ≫ₕ ofSet f.source f.open_source) ≫ₕ e' := by rw [trans_assoc]
    _ ≈ e.symm.restr s ≫ₕ e' := by rw [trans_of_set']; apply refl
    _ ≈ (e.symm ≫ₕ e').restr s := by rw [restr_trans]
  exact G.mem_of_eqOnSource C (Setoid.symm D)

open OpenPartialHomeomorph in
/-- The maximal atlas of a structure groupoid is stable under equivalence. -/
/-
**StructureGroupoid.mem_maximalAtlas_of_eqOnSource** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StructureGroupoid.mem_maximalAtlas_of_eqOnSource {e e' : OpenPartialHomeom
orph M H} (h : e' ≈ e) (he : e in G.maximalAtlas M) : e' in G.maximalAtlas M
参数：h : e' ≈ e；he : e in G.maximalAtlas M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_maximalAtlas_iff`：mem_maximalAtlas_iff {e : OpenPartialHomeomorph M 
H} : e in G.maximalAtlas M ↔ forall e' in atlas H M, e.symm ≫ₕ e' in G ∧ e'.symm
 ≫ₕ e in G
· 使用定理 `StructureGroupoid.mem_of_eqOnSource`：StructureGroupoid.mem_of_eqOnSource
 (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (h :
 e' ≈ e) : e' in G
· 使用定理 `OpenPartialHomeomorph.EqOnSource.trans'`：∀ {X : Type u_1} {Y : Type u_3}
 {Z : Type u_5} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [ins
t_2 : TopologicalSpace Z] {e …
· 使用定理 `OpenPartialHomeomorph.EqOnSource.symm'`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e e' : OpenPartialH
omeomorph X Y}, e ≈ e' → e.s…
· 使用定理 `OpenPartialHomeomorph.eqOnSource_refl`：eqOnSource_refl : e ≈ e

--- 原说明 ---
The maximal atlas of a structure groupoid is stable under equivalence.
-/
lemma StructureGroupoid.mem_maximalAtlas_of_eqOnSource {e e' : OpenPartialHomeomorph M H}
    (h : e' ≈ e) (he : e ∈ G.maximalAtlas M) : e' ∈ G.maximalAtlas M := by
  intro e'' he''
  obtain ⟨l, r⟩ := mem_maximalAtlas_iff.mp he e'' he''
  exact ⟨G.mem_of_eqOnSource l (EqOnSource.trans' (EqOnSource.symm' h) (e''.eqOnSource_refl)),
         G.mem_of_eqOnSource r (EqOnSource.trans' (e''.symm).eqOnSource_refl h)⟩

variable (G)

/-- In the model space, the identity is in any maximal atlas. -/
/-
**StructureGroupoid.id_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StructureGroupoid.id_mem_maximalAtlas : OpenPartialHomeomorph.refl H in G.
maximalAtlas H
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.subset_maximalAtlas`：StructureGroupoid.subset_maximalA
tlas [HasGroupoid M G] : atlas H M subseteq G.maximalAtlas M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the model space, the identity is in any maximal atlas.
-/
theorem StructureGroupoid.id_mem_maximalAtlas : OpenPartialHomeomorph.refl H ∈ G.maximalAtlas H :=
  G.subset_maximalAtlas <| by simp

/-- In the model space, any element of the groupoid is in the maximal atlas. -/
/-
**StructureGroupoid.mem_maximalAtlas_of_mem_groupoid** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：StructureGroupoid.mem_maximalAtlas_of_mem_groupoid {f : OpenPartialHomeomo
rph H H} (hf : f in G) : f in G.maximalAtlas H
参数：hf : f in G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.trans`：StructureGroupoid.trans (G : StructureGroupoid 
H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (he' : e' in G) : e ≫ₕ e' in
 G
· 使用定理 `StructureGroupoid.symm`：StructureGroupoid.symm (G : StructureGroupoid H)
 {e : OpenPartialHomeomorph H H} (he : e in G) : e.symm in G
· 使用定理 `StructureGroupoid.id_mem`：StructureGroupoid.id_mem (G : StructureGroupoi
d H) : OpenPartialHomeomorph.refl H in G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
In the model space, any element of the groupoid is in the maximal atlas.
-/
theorem StructureGroupoid.mem_maximalAtlas_of_mem_groupoid {f : OpenPartialHomeomorph H H}
    (hf : f ∈ G) : f ∈ G.maximalAtlas H := by
  rintro e (rfl : e = OpenPartialHomeomorph.refl H)
  exact ⟨G.trans (G.symm hf) G.id_mem, G.trans (G.symm G.id_mem) hf⟩
/-
**StructureGroupoid.maximalAtlas_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StructureGroupoid.maximalAtlas_mono {G G' : StructureGroupoid H} (h : G <=
 G') : G.maximalAtlas M subseteq G'.maximalAtlas M
参数：h : G <= G'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem StructureGroupoid.maximalAtlas_mono {G G' : StructureGroupoid H} (h : G ≤ G') :
    G.maximalAtlas M ⊆ G'.maximalAtlas M :=
  fun _ he e' he' ↦ ⟨h (he e' he').1, h (he e' he').2⟩
/-
**restr_mem_maximalAtlas_aux1** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem restr_mem_maximalAtlas_aux1 [ClosedUnderRestriction G]
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ G.maximalAtlas M) (he' : e' ∈ atlas H M)
    {s : Set M} (hs : IsOpen s) :
    (e.restr s).symm ≫ₕ e' ∈ G := by
  have hs'' : IsOpen (e '' (e.source ∩ s)) := by
    rw [isOpen_image_iff_of_subset_source _ inter_subset_left]
    exact e.open_source.inter hs
  have : (e.restr (e.source ∩ s)).symm ≫ₕ e' ∈ G := by
    apply G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').1 hs'')
    exact e.restr_symm_trans (e.open_source.inter hs) hs'' inter_subset_left
  refine G.mem_of_eqOnSource this ?_
  exact EqOnSource.trans' (Setoid.symm e.restr_inter_source).symm' (eqOnSource_refl e')
/-
**restr_mem_maximalAtlas_aux2** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem restr_mem_maximalAtlas_aux2 [ClosedUnderRestriction G]
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ G.maximalAtlas M) (he' : e' ∈ atlas H M)
    {s : Set M} (hs : IsOpen s) :
    e'.symm ≫ₕ e.restr s ∈ G := by
  have hs'' : IsOpen (e' '' (e'.source ∩ s)) := by
    rw [isOpen_image_iff_of_subset_source e' inter_subset_left]
    exact e'.open_source.inter hs
  have ht : IsOpen (e'.target ∩ e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  exact G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').2 ht) (e.symm_trans_restr e' hs)

/-- If a structure groupoid `G` is closed under restriction, for any chart `e` in the maximal atlas,
the restriction `e.restr s` to an open set `s` is also in the maximal atlas. -/
/-
**restr_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：restr_mem_maximalAtlas [ClosedUnderRestriction G] {e : OpenPartialHomeomor
ph M H} (he : e in G.maximalAtlas M) {s : Set M} (hs : IsOpen s) : e.restr s in 
G.maximalAtlas M
参数：he : e in G.maximalAtlas M；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Geometry.Manifold.HasGroupoid.0.restr_mem_maximalAtlas_
aux1`：∀ {H : Type u} {M : Type u_2} [inst : TopologicalSpace H] [inst_1 : Topolo
gicalSpace M] [inst_2 : ChartedSpace H M]   (G : StructureGroupoid…
· 使用定理 `_private.Mathlib.Geometry.Manifold.HasGroupoid.0.restr_mem_maximalAtlas_
aux2`：∀ {H : Type u} {M : Type u_2} [inst : TopologicalSpace H] [inst_1 : Topolo
gicalSpace M] [inst_2 : ChartedSpace H M]   (G : StructureGroupoid…

--- 原说明 ---
If a structure groupoid `G` is closed under restriction, for any chart `e` in th
e maximal atlas,
the restriction `e.restr s` to an open set `s` is also in the maximal atlas.
-/
theorem restr_mem_maximalAtlas [ClosedUnderRestriction G]
    {e : OpenPartialHomeomorph M H} (he : e ∈ G.maximalAtlas M) {s : Set M} (hs : IsOpen s) :
    e.restr s ∈ G.maximalAtlas M :=
  fun _e' he' ↦ ⟨restr_mem_maximalAtlas_aux1 G he he' hs, restr_mem_maximalAtlas_aux2 G he he' hs⟩

end MaximalAtlas

section Singleton

variable {α : Type*} [TopologicalSpace α]

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph α H)

/-- If a single open partial homeomorphism `e` from a space `α` into `H` has source covering the
whole space `α`, then that open partial homeomorphism induces an `H`-charted space structure on `α`.
(This condition is equivalent to `e` being an open embedding of `α` into `H`; see
`IsOpenEmbedding.singletonChartedSpace`.) -/
@[instance_reducible]
/-
**OpenPartialHomeomorph.singletonChartedSpace** 是 Mathlib 中的一个定义，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：singletonChartedSpace (h : e.source = Set.univ) : ChartedSpace H α where a
tlas
参数：h : e.source = Set.univ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a single open partial homeomorphism `e` from a space `α` into `H` has source 
covering the
whole space `α`, then that open partial homeomorphism induces an `H`-charted spa
ce structure on `α`.
(This condition is equivalent to `e` being an open embedding of `α` into `H`; se
e
`IsOpenEmbedding.singletonChartedSpace`.)
-/
def singletonChartedSpace (h : e.source = Set.univ) : ChartedSpace H α where
  atlas := {e}
  chartAt _ := e
  mem_chart_source _ := by rw [h]; apply mem_univ
  chart_mem_atlas _ := by tauto

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq** 是 Mathlib 中的一个定理，位于命名
空间 `OpenPartialHomeomorph`。
形式化陈述：singletonChartedSpace_chartAt_eq (h : e.source = Set.univ) {x : α} : @char
tAt H _ α _ (e.singletonChartedSpace h) x = e
参数：h : e.source = Set.univ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singletonChartedSpace_chartAt_eq (h : e.source = Set.univ) {x : α} :
    @chartAt H _ α _ (e.singletonChartedSpace h) x = e :=
  rfl
/-
**OpenPartialHomeomorph.singletonChartedSpace_chartAt_source** 是 Mathlib 中的一个定理，
位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：singletonChartedSpace_chartAt_source (h : e.source = Set.univ) {x : α} : (
@chartAt H _ α _ (e.singletonChartedSpace h) x).source = Set.univ
参数：h : e.source = Set.univ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singletonChartedSpace_chartAt_source (h : e.source = Set.univ) {x : α} :
    (@chartAt H _ α _ (e.singletonChartedSpace h) x).source = Set.univ :=
  h
/-
**OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq** 是 Mathlib 中的一个定理，位于
命名空间 `OpenPartialHomeomorph`。
形式化陈述：singletonChartedSpace_mem_atlas_eq (h : e.source = Set.univ) (e' : OpenPar
tialHomeomorph α H) (h' : e' in (e.singletonChartedSpace h).atlas) : e' = e
参数：h : e.source = Set.univ；e' : OpenPartialHomeomorph α H；h' : e' in (e.singleto
nChartedSpace h).atlas。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singletonChartedSpace_mem_atlas_eq (h : e.source = Set.univ)
    (e' : OpenPartialHomeomorph α H) (h' : e' ∈ (e.singletonChartedSpace h).atlas) : e' = e :=
  h'

/-- Given an open partial homeomorphism `e` from a space `α` into `H`, if its source covers the
whole space `α`, then the induced charted space structure on `α` is `HasGroupoid G` for any
/-
**OpenPartialHomeomorph.groupoid** 是 Mathlib 中的一个结构，位于命名空间 `OpenPartialHomeomorp
h`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure groupoid `G` which is closed under restrictions. -/
/-
**OpenPartialHomeomorph.singleton_hasGroupoid** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：singleton_hasGroupoid (h : e.source = Set.univ) (G : StructureGroupoid H) 
[ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ (e.singletonChartedSpace h) G
参数：h : e.source = Set.univ；G : StructureGroupoid H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq`：singletonChart
edSpace_mem_atlas_eq (h : e.source = Set.univ) (e' : OpenPartialHomeomorph α H) 
(h' : e' in (e.singletonChartedSpace h).atlas)…
· 使用定理 `StructureGroupoid.mem_of_eqOnSource`：StructureGroupoid.mem_of_eqOnSource
 (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (h :
 e' ≈ e) : e' in G
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `closedUnderRestriction_iff_id_le`：closedUnderRestriction_iff_id_le (G : 
StructureGroupoid H) : ClosedUnderRestriction G ↔ idRestrGroupoid <= G
· 使用定理 `StructureGroupoid.le_iff`：StructureGroupoid.le_iff {G₁ G₂ : StructureGro
upoid H} : G₁ <= G₂ ↔ forall e, e in G₁ -> e in G₂
· 使用定理 `idRestrGroupoid_mem`：idRestrGroupoid_mem {s : Set H} (hs : IsOpen s) : o
fSet s hs in @idRestrGroupoid H _
· 使用定理 `OpenPartialHomeomorph.symm_trans_self`：symm_trans_self : e.symm.trans e 
≈ OpenPartialHomeomorph.ofSet e.target e.open_target

--- 原说明 ---
Given an open partial homeomorphism `e` from a space `α` into `H`, if its source
 covers the
whole space `α`, then the induced charted space structure on `α` is `HasGroupoid
 G` for any
structure groupoid `G` which is closed under restrictions.
-/
theorem singleton_hasGroupoid (h : e.source = Set.univ) (G : StructureGroupoid H)
    [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ (e.singletonChartedSpace h) G :=
  { __ := e.singletonChartedSpace h
    compatible := by
      intro e' e'' he' he''
      rw [e.singletonChartedSpace_mem_atlas_eq h e' he',
        e.singletonChartedSpace_mem_atlas_eq h e'' he'']
      refine G.mem_of_eqOnSource ?_ e.symm_trans_self
      have hle : idRestrGroupoid ≤ G := (closedUnderRestriction_iff_id_le G).mp (by assumption)
      exact StructureGroupoid.le_iff.mp hle _ (idRestrGroupoid_mem _) }

end OpenPartialHomeomorph

namespace Topology.IsOpenEmbedding

variable [Nonempty α]

/-- An open embedding of `α` into `H` induces an `H`-charted space structure on `α`.
See `OpenPartialHomeomorph.singletonChartedSpace`. -/
@[instance_reducible]
/-
**Topology.IsOpenEmbedding.singletonChartedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Topo
logy.IsOpenEmbedding`。
形式化陈述：singletonChartedSpace {f : α -> H} (h : IsOpenEmbedding f) : ChartedSpace 
H α
参数：h : IsOpenEmbedding f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source`：∀ {X : Type u_1
} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : 
X → Y)   (h : Topology.IsOpenEmbedding f) [in…

--- 原说明 ---
An open embedding of `α` into `H` induces an `H`-charted space structure on `α`.
See `OpenPartialHomeomorph.singletonChartedSpace`.
-/
def singletonChartedSpace {f : α → H} (h : IsOpenEmbedding f) : ChartedSpace H α :=
  (h.toOpenPartialHomeomorph f).singletonChartedSpace (toOpenPartialHomeomorph_source _ _)
/-
**Topology.IsOpenEmbedding.singletonChartedSpace_chartAt_eq** 是 Mathlib 中的一个定理，位
于命名空间 `Topology.IsOpenEmbedding`。
形式化陈述：singletonChartedSpace_chartAt_eq {f : α -> H} (h : IsOpenEmbedding f) {x :
 α} : ⇑(@chartAt H _ α _ h.singletonChartedSpace x) = f
参数：h : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singletonChartedSpace_chartAt_eq {f : α → H} (h : IsOpenEmbedding f) {x : α} :
    ⇑(@chartAt H _ α _ h.singletonChartedSpace x) = f :=
  rfl
/-
**Topology.IsOpenEmbedding.singleton_hasGroupoid** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.IsOpenEmbedding`。
形式化陈述：singleton_hasGroupoid {f : α -> H} (h : IsOpenEmbedding f) (G : StructureG
roupoid H) [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ h.singletonChartedS
pace G
参数：h : IsOpenEmbedding f；G : StructureGroupoid H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.singleton_hasGroupoid`：singleton_hasGroupoid (h : 
e.source = Set.univ) (G : StructureGroupoid H) [ClosedUnderRestriction G] : @Has
Groupoid _ _ _ _ (e.singletonChar…
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source`：∀ {X : Type u_1
} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : 
X → Y)   (h : Topology.IsOpenEmbedding f) [in…
-/
theorem singleton_hasGroupoid {f : α → H} (h : IsOpenEmbedding f) (G : StructureGroupoid H)
    [ClosedUnderRestriction G] : @HasGroupoid _ _ _ _ h.singletonChartedSpace G :=
  (h.toOpenPartialHomeomorph f).singleton_hasGroupoid (toOpenPartialHomeomorph_source _ _) G

end Topology.IsOpenEmbedding

end Singleton

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (G : StructureGroupoid H) [HasGroupoid M G]
variable (s : Opens M)

/-- An open subset of a charted space is naturally a charted space. -/
/-
**TopologicalSpace.Opens.instChartedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Topological
Space.Opens`。
形式化陈述：{H : Type u} →   {M : Type u_2} →     [inst : TopologicalSpace H] →       
[inst_1 : TopologicalSpace M] → [ChartedSpace H M] → (s : TopologicalSpace.Opens
 M) → ChartedSpace H ↥s
参数：s : TopologicalSpace.Opens M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open subset of a charted space is naturally a charted space.
-/
protected instance instChartedSpace : ChartedSpace H s where
  atlas := ⋃ x : s, {(chartAt H x.1).subtypeRestr ⟨x⟩}
  chartAt x := (chartAt H x.1).subtypeRestr ⟨x⟩
  mem_chart_source x := ⟨trivial, mem_chart_source H x.1⟩
  chart_mem_atlas x := by
    simp only [mem_iUnion, mem_singleton_iff]
    use x
/-
**TopologicalSpace.Opens.chartAt_eq** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.
Opens`。
形式化陈述：chartAt_eq {s : Opens M} {x : s} : chartAt H x = (chartAt H x.1).subtypeRe
str ⟨x⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chartAt_eq {s : Opens M} {x : s} : chartAt H x = (chartAt H x.1).subtypeRestr ⟨x⟩ := rfl

/-- If `s` is a non-empty open subset of `M`, every chart of `s` is the restriction
of some chart on `M`. -/
/-
**TopologicalSpace.Opens.chart_eq** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：chart_eq {s : Opens M} (hs : Nonempty s) {e : OpenPartialHomeomorph s H} (
he : e in atlas H s) : exists x : s, e = (chartAt H (x : M)).subtypeRestr hs
参数：hs : Nonempty s；he : e in atlas H s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `s` is a non-empty open subset of `M`, every chart of `s` is the restriction
of some chart on `M`.
-/
lemma chart_eq {s : Opens M} (hs : Nonempty s) {e : OpenPartialHomeomorph s H}
    (he : e ∈ atlas H s) : ∃ x : s, e = (chartAt H (x : M)).subtypeRestr hs := by
  rcases he with ⟨xset, ⟨x, hx⟩, he⟩
  exact ⟨x, mem_singleton_iff.mp (by convert! he)⟩

/-- If `t` is a non-empty open subset of `H`,
every chart of `t` is the restriction of some chart on `H`. -/
-- XXX: can I unify this with `chart_eq`?
/-
**TopologicalSpace.Opens.chart_eq'** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：chart_eq' {t : Opens H} (ht : Nonempty t) {e' : OpenPartialHomeomorph t H}
 (he' : e' in atlas H t) : exists x : t, e' = (chartAt H ↑x).subtypeRestr ht
参数：ht : Nonempty t；he' : e' in atlas H t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopologicalSpace.Opens.chart_eq`：chart_eq {s : Opens M} (hs : Nonempty s
) {e : OpenPartialHomeomorph s H} (he : e in atlas H s) : exists x : s, e = (cha
rtAt H (x : M)).subty…
-/
lemma chart_eq' {t : Opens H} (ht : Nonempty t) {e' : OpenPartialHomeomorph t H}
    (he' : e' ∈ atlas H t) : ∃ x : t, e' = (chartAt H ↑x).subtypeRestr ht :=
  chart_eq ht he'

/-- If a groupoid `G` is `ClosedUnderRestriction`, then an open subset of a space which is
`HasGroupoid G` is naturally `HasGroupoid G`. -/
/-
**TopologicalSpace.Opens.instHasGroupoid** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：∀ {H : Type u} {M : Type u_2} [inst : TopologicalSpace H] [inst_1 : Topolo
gicalSpace M] [inst_2 : ChartedSpace H M]   (G : StructureGroupoid H) [HasGroupo
id M G] (s : TopologicalSpace.Opens M) [ClosedUnderRestriction G],   HasGroupoid
 (↥s) G
参数：G : StructureGroupoid H；s : TopologicalSpace.Opens M；↥s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.mem_of_eqOnSource`：StructureGroupoid.mem_of_eqOnSource
 (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (h :
 e' ≈ e) : e' in G
· 使用定理 `closedUnderRestriction'`：closedUnderRestriction' {G : StructureGroupoid 
H} [ClosedUnderRestriction G] {e : OpenPartialHomeomorph H H} (he : e in G) {s :
 Set H} (hs :…
· 使用定理 `StructureGroupoid.compatible`：StructureGroupoid.compatible {H : Type*} [
TopologicalSpace H] (G : StructureGroupoid H) {M : Type*} [TopologicalSpace M] [
ChartedSpace H M] …
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage_symm`：isOpen_inter_preimage_
symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target inter e.symm ⁻¹' s)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr`：subtypeRestr
_symm_trans_subtypeRestr (f f' : OpenPartialHomeomorph X Y) : (f.subtypeRestr hs
).symm.trans (f'.subtypeRestr hs) ≈ (f.symm.tran…

--- 原说明 ---
If a groupoid `G` is `ClosedUnderRestriction`, then an open subset of a space wh
ich is
`HasGroupoid G` is naturally `HasGroupoid G`.
-/
protected instance instHasGroupoid [ClosedUnderRestriction G] : HasGroupoid s G where
  compatible := by
    rintro e e' ⟨_, ⟨x, hc⟩, he⟩ ⟨_, ⟨x', hc'⟩, he'⟩
    rw [hc.symm, mem_singleton_iff] at he
    rw [hc'.symm, mem_singleton_iff] at he'
    rw [he, he']
    refine G.mem_of_eqOnSource ?_
      (subtypeRestr_symm_trans_subtypeRestr (s := s) _ (chartAt H x) (chartAt H x'))
    apply closedUnderRestriction'
    · exact G.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
    · exact isOpen_inter_preimage_symm (chartAt _ _) s.2
/-
**TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq** 是 Mathlib 中的一个定
理，位于命名空间 `TopologicalSpace.Opens`。
形式化陈述：chartAt_subtype_val_symm_eventuallyEq (U : Opens M) {x : U} : (chartAt H x
.val).symm =ᶠ[𝓝 (chartAt H x.val x.val)] Subtype.val ∘ (chartAt H x).symm
参数：U : Opens M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.map_subtype_source`：map_subtype_source {x : s} (hx
e : (x : X) in e.source) : e x in (e.subtypeRestr hs).target
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_symm_eqOn`：subtypeRestr_symm_eqOn {U 
: Opens X} (hU : Nonempty U) : EqOn e.symm (Subtype.val ∘ (e.subtypeRestr hU).sy
mm) (e.subtypeRestr hU).target
-/
theorem chartAt_subtype_val_symm_eventuallyEq (U : Opens M) {x : U} :
    (chartAt H x.val).symm =ᶠ[𝓝 (chartAt H x.val x.val)] Subtype.val ∘ (chartAt H x).symm := by
  set e := chartAt H x.val
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target ∈ 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
  exact Filter.eventuallyEq_of_mem heUx_nhds (e.subtypeRestr_symm_eqOn ⟨x⟩)
/-
**TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq** 是 Mathlib 中的一个定理，
位于命名空间 `TopologicalSpace.Opens`。
形式化陈述：chartAt_inclusion_symm_eventuallyEq {U V : Opens M} (hUV : U <= V) {x : U}
 : (chartAt H (Opens.inclusion hUV x)).symm =ᶠ[𝓝 (chartAt H (Opens.inclusion hUV
 x) (Set.inclusion hUV x))] Opens.inclusion hUV ∘ (chartAt H x).symm
参数：hUV : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.map_subtype_source`：map_subtype_source {x : s} (hx
e : (x : X) in e.source) : e x in (e.subtypeRestr hs).target
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_symm_eqOn_of_le`：subtypeRestr_symm_eq
On_of_le {U V : Opens X} (hU : Nonempty U) (hV : Nonempty V) (hUV : U <= V) : Eq
On (e.subtypeRestr hV).symm (Set.inclusi…
-/
theorem chartAt_inclusion_symm_eventuallyEq {U V : Opens M} (hUV : U ≤ V) {x : U} :
    (chartAt H (Opens.inclusion hUV x)).symm
    =ᶠ[𝓝 (chartAt H (Opens.inclusion hUV x) (Set.inclusion hUV x))]
    Opens.inclusion hUV ∘ (chartAt H x).symm := by
  set e := chartAt H (x : M)
  have heUx_nhds : (e.subtypeRestr ⟨x⟩).target ∈ 𝓝 (e x) := by
    apply (e.subtypeRestr ⟨x⟩).open_target.mem_nhds
    exact e.map_subtype_source ⟨x⟩ (mem_chart_source _ _)
  exact Filter.eventuallyEq_of_mem heUx_nhds <| e.subtypeRestr_symm_eqOn_of_le ⟨x⟩
    ⟨Opens.inclusion hUV x⟩ hUV
end TopologicalSpace.Opens

/-- Restricting a chart of `M` to an open subset `s` yields a chart in the maximal atlas of `s`.

NB. We cannot deduce membership in `atlas H s` in general: by definition, this atlas contains
precisely the restriction of each preferred chart at `x ∈ s` --- whereas `atlas H M`
can contain more charts than these. -/
/-
**StructureGroupoid.subtypeRestr_mem_maximalAtlas** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StructureGroupoid.subtypeRestr_mem_maximalAtlas {e : OpenPartialHomeomorph
 M H} (he : e in atlas H M) {s : Opens M} (hs : Nonempty s) {G : StructureGroupo
id H} [HasGroupoid M G] [ClosedUnderRestriction G] : e.subtypeRestr hs in G.maxi
malAtlas s
参数：he : e in atlas H M；hs : Nonempty s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopologicalSpace.Opens.chart_eq`：chart_eq {s : Opens M} (hs : Nonempty s
) {e : OpenPartialHomeomorph s H} (he : e in atlas H s) : exists x : s, e = (cha
rtAt H (x : M)).subty…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.trans_restricted`：StructureGroupoid.trans_restricted {
e e' : OpenPartialHomeomorph M H} {G : StructureGroupoid H} (he : e in atlas H M
) (he' : e' in atlas H M…
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M

--- 原说明 ---
Restricting a chart of `M` to an open subset `s` yields a chart in the maximal a
tlas of `s`.

NB. We cannot deduce membership in `atlas H s` in general: by definition, this a
tlas contains
precisely the restriction of each preferred chart at `x ∈ s` --- whereas `atlas 
H M`
can contain more charts than these.
-/
lemma StructureGroupoid.subtypeRestr_mem_maximalAtlas {e : OpenPartialHomeomorph M H}
    (he : e ∈ atlas H M) {s : Opens M} (hs : Nonempty s) {G : StructureGroupoid H} [HasGroupoid M G]
    [ClosedUnderRestriction G] : e.subtypeRestr hs ∈ G.maximalAtlas s := by
  intro e' he'
  -- `e'` is the restriction of some chart of `M` at `x`,
  obtain ⟨x, this⟩ := Opens.chart_eq hs he'
  rw [this]
  -- The transition functions between the unrestricted charts lie in the groupoid,
  -- the transition functions of the restriction are the restriction of the transition function.
  exact ⟨G.trans_restricted he (chart_mem_atlas H (x : M)) hs,
         G.trans_restricted (chart_mem_atlas H (x : M)) he hs⟩

/-! ### Structomorphisms -/

/-- A `G`-diffeomorphism between two charted spaces is a homeomorphism which, when read in the
charts, belongs to `G`. We avoid the word diffeomorph as it is too related to the smooth category,
and use structomorph instead. -/
/-
**Structomorph** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{H : Type u} →   [inst : TopologicalSpace H] →     StructureGroupoid H →  
     (M : Type u_5) →         (M' : Type u_6) →           [inst_1 : TopologicalS
pace M] →             [inst_2 : TopologicalSpace M'] → [ChartedSpace H M] → [Cha
rtedSpace H M'] → Type (max u_5 u_6)
参数：M : Type u_5；M' : Type u_6；max u_5 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `G`-diffeomorphism between two charted spaces is a homeomorphism which, when r
ead in the
charts, belongs to `G`. We avoid the word diffeomorph as it is too related to th
e smooth category,
and use structomorph instead.
-/
structure Structomorph (G : StructureGroupoid H) (M : Type*) (M' : Type*) [TopologicalSpace M]
  [TopologicalSpace M'] [ChartedSpace H M] [ChartedSpace H M'] extends Homeomorph M M' where
  mem_groupoid : ∀ c : OpenPartialHomeomorph M H, ∀ c' : OpenPartialHomeomorph M' H, c ∈ atlas H M →
    c' ∈ atlas H M' → c.symm ≫ₕ toHomeomorph.toOpenPartialHomeomorph ≫ₕ c' ∈ G

variable [TopologicalSpace M'] [TopologicalSpace M''] {G : StructureGroupoid H} [ChartedSpace H M']
  [ChartedSpace H M'']

/-- The identity is a diffeomorphism of any charted space, for any groupoid. -/
/-
**Structomorph.refl** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Structomorph.refl (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [Has
Groupoid M G] : Structomorph G M M
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity is a diffeomorphism of any charted space, for any groupoid.
-/
def Structomorph.refl (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G] :
    Structomorph G M M :=
  { Homeomorph.refl M with
    mem_groupoid := fun c c' hc hc' ↦ by
      change OpenPartialHomeomorph.symm c ≫ₕ OpenPartialHomeomorph.refl M ≫ₕ c' ∈ G
      rw [OpenPartialHomeomorph.refl_trans]
      exact G.compatible hc hc' }

/-- The inverse of a structomorphism is a structomorphism. -/
/-
**Structomorph.symm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Structomorph.symm (e : Structomorph G M M') : Structomorph G M' M
参数：e : Structomorph G M M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a structomorphism is a structomorphism.
-/
def Structomorph.symm (e : Structomorph G M M') : Structomorph G M' M :=
  { e.toHomeomorph.symm with
    mem_groupoid := by
      intro c c' hc hc'
      have : (c'.symm ≫ₕ e.toHomeomorph.toOpenPartialHomeomorph ≫ₕ c).symm ∈ G :=
        G.symm (e.mem_groupoid c' c hc' hc)
      rwa [trans_symm_eq_symm_trans_symm, trans_symm_eq_symm_trans_symm, symm_symm, trans_assoc]
        at this }

/-- The composition of structomorphisms is a structomorphism. -/
/-
**Structomorph.trans** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Structomorph.trans (e : Structomorph G M M') (e' : Structomorph G M' M'') 
: Structomorph G M M''
参数：e : Structomorph G M M'；e' : Structomorph G M' M''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of structomorphisms is a structomorphism.
-/
def Structomorph.trans (e : Structomorph G M M') (e' : Structomorph G M' M'') :
    Structomorph G M M'' :=
  { Homeomorph.trans e.toHomeomorph e'.toHomeomorph with
    mem_groupoid := by
      /- Let c and c' be two charts in M and M''. We want to show that e' ∘ e is smooth in these
      charts, around any point x. For this, let y = e (c⁻¹ x), and consider a chart g around y.
      Then g ∘ e ∘ c⁻¹ and c' ∘ e' ∘ g⁻¹ are both smooth as e and e' are structomorphisms, so
      their composition is smooth, and it coincides with c' ∘ e' ∘ e ∘ c⁻¹ around x. -/
      intro c c' hc hc'
      refine G.locality fun x hx ↦ ?_
      let f₁ := e.toHomeomorph.toOpenPartialHomeomorph
      let f₂ := e'.toHomeomorph.toOpenPartialHomeomorph
      let f := (e.toHomeomorph.trans e'.toHomeomorph).toOpenPartialHomeomorph
      have feq : f = f₁ ≫ₕ f₂ := Homeomorph.trans_toOpenPartialHomeomorph _ _
      -- define the atlas g around y
      let y := (c.symm ≫ₕ f₁) x
      let g := chartAt (H := H) y
      have hg₁ := chart_mem_atlas (H := H) y
      have hg₂ := mem_chart_source (H := H) y
      let s := (c.symm ≫ₕ f₁).source ∩ c.symm ≫ₕ f₁ ⁻¹' g.source
      have open_s : IsOpen s := by
        apply (c.symm ≫ₕ f₁).continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
      have : x ∈ s := by
        constructor
        · simp only [f₁, trans_source, preimage_univ, inter_univ,
            Homeomorph.toOpenPartialHomeomorph_source]
          rw [trans_source] at hx
          exact hx.1
        · exact hg₂
      refine ⟨s, open_s, this, ?_⟩
      let F₁ := (c.symm ≫ₕ f₁ ≫ₕ g) ≫ₕ g.symm ≫ₕ f₂ ≫ₕ c'
      have A : F₁ ∈ G := G.trans (e.mem_groupoid c g hc hg₁) (e'.mem_groupoid g c' hg₁ hc')
      let F₂ := (c.symm ≫ₕ f ≫ₕ c').restr s
      have : F₁ ≈ F₂ := calc
        F₁ ≈ c.symm ≫ₕ f₁ ≫ₕ (g ≫ₕ g.symm) ≫ₕ f₂ ≫ₕ c' := by
            simp only [F₁, trans_assoc, _root_.refl]
        _ ≈ c.symm ≫ₕ f₁ ≫ₕ ofSet g.source g.open_source ≫ₕ f₂ ≫ₕ c' :=
          EqOnSource.trans' (_root_.refl _) (EqOnSource.trans' (_root_.refl _)
            (EqOnSource.trans' (self_trans_symm g) (_root_.refl _)))
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ ofSet g.source g.open_source) ≫ₕ f₂ ≫ₕ c' := by
          simp only [trans_assoc, _root_.refl]
        _ ≈ (c.symm ≫ₕ f₁).restr s ≫ₕ f₂ ≫ₕ c' := by rw [trans_of_set']
        _ ≈ ((c.symm ≫ₕ f₁) ≫ₕ f₂ ≫ₕ c').restr s := by rw [restr_trans]
        _ ≈ (c.symm ≫ₕ (f₁ ≫ₕ f₂) ≫ₕ c').restr s := by
          simp only [trans_assoc, _root_.refl]
        _ ≈ F₂ := by simp only [F₂, feq, _root_.refl]
      have : F₂ ∈ G := G.mem_of_eqOnSource A (Setoid.symm this)
      exact this }

/-- Restricting a chart to its source `s ⊆ M` yields a chart in the maximal atlas of `s`. -/
/-
**StructureGroupoid.restriction_mem_maximalAtlas_subtype** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：StructureGroupoid.restriction_mem_maximalAtlas_subtype {e : OpenPartialHom
eomorph M H} (he : e in atlas H M) (hs : Nonempty e.source) [HasGroupoid M G] [C
losedUnderRestriction G] : let s
参数：he : e in atlas H M；hs : Nonempty e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `Set.MapsTo.nonempty`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Se
t β} {f : α → β}, Set.MapsTo f s t → s.Nonempty → t.Nonempty
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `TopologicalSpace.Opens.chart_eq`：chart_eq {s : Opens M} (hs : Nonempty s
) {e : OpenPartialHomeomorph s H} (he : e in atlas H s) : exists x : s, e = (cha
rtAt H (x : M)).subty…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `chartAt_self_eq`：chartAt_self_eq {H : Type*} [TopologicalSpace H] {x : H
} : chartAt H x = OpenPartialHomeomorph.refl H
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_def`：subtypeRestr_def : e.subtypeRest
r hs = (s.openPartialHomeomorphSubtypeCoe hs).trans e
· 使用定理 `OpenPartialHomeomorph.trans_refl`：trans_refl : e.trans (OpenPartialHomeo
morph.refl Y) = e
· 使用定理 `OpenPartialHomeomorph.eqOnSource_iff`：eqOnSource_iff (e e' : OpenPartial
Homeomorph X Y) : EqOnSource e e' ↔ PartialEquiv.EqOnSource e.toPartialEquiv e'.
toPartialEquiv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_source`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   e.t
oOpenPartialHomeomorph.source =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_apply`：∀ {X : Type u_1} {Y : Type u_3
} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   ↑e.t
oOpenPartialHomeomorph = ⇑e
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `OpenPartialHomeomorph.subtypeRestr_source`：subtypeRestr_source : (e.subt
ypeRestr hs).source = (↑) ⁻¹' e.source
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用引理 `StructureGroupoid.mem_maximalAtlas_of_eqOnSource`：StructureGroupoid.mem_
maximalAtlas_of_eqOnSource {e e' : OpenPartialHomeomorph M H} (h : e' ≈ e) (he :
 e in G.maximalAtlas M) : e' in G.maxi…
· 使用引理 `StructureGroupoid.subtypeRestr_mem_maximalAtlas`：StructureGroupoid.subty
peRestr_mem_maximalAtlas {e : OpenPartialHomeomorph M H} (he : e in atlas H M) {
s : Opens M} (hs : Nonempty s) {G : S…

--- 原说明 ---
Restricting a chart to its source `s ⊆ M` yields a chart in the maximal atlas of
 `s`.
-/
theorem StructureGroupoid.restriction_mem_maximalAtlas_subtype
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (hs : Nonempty e.source) [HasGroupoid M G] [ClosedUnderRestriction G] :
    let s := { carrier := e.source, is_open' := e.open_source : Opens M }
    let t := { carrier := e.target, is_open' := e.open_target : Opens H }
    ∀ c' ∈ atlas H t,
      e.toHomeomorphSourceTarget.toOpenPartialHomeomorph ≫ₕ c' ∈ G.maximalAtlas s := by
  intro s t c' hc'
  have : Nonempty t := nonempty_coe_sort.mpr (e.mapsTo.nonempty (nonempty_coe_sort.mp hs))
  obtain ⟨x, hc'⟩ := Opens.chart_eq this hc'
  -- As H has only one chart, `chartAt H x` is the identity: i.e., `c'` is the inclusion.
  rw [hc', (chartAt_self_eq)]
  -- Our expression equals this chart, at least on its source.
  rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_refl]
  let goal :=
    e.toHomeomorphSourceTarget.toOpenPartialHomeomorph ≫ₕ (t.openPartialHomeomorphSubtypeCoe this)
  have : goal ≈ e.subtypeRestr (s := s) hs :=
    (goal.eqOnSource_iff (e.subtypeRestr (s := s) hs)).mpr
      ⟨by
        simp only [trans_toPartialEquiv, PartialEquiv.trans_source,
          Homeomorph.toOpenPartialHomeomorph_source, toFun_eq_coe,
          Homeomorph.toOpenPartialHomeomorph_apply, Opens.openPartialHomeomorphSubtypeCoe_source,
          preimage_univ, inter_self, subtypeRestr_source, goal, s]
        exact Subtype.coe_preimage_self _ |>.symm, by intro _ _; rfl⟩
  exact G.mem_maximalAtlas_of_eqOnSource (M := s) this (G.subtypeRestr_mem_maximalAtlas he hs)

/-- Each chart of a charted space is a structomorphism between its source and target. -/
/-
**OpenPartialHomeomorph.toStructomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.toStructomorph {e : OpenPartialHomeomorph M H} (he :
 e in atlas H M) [HasGroupoid M G] [ClosedUnderRestriction G] : let s : Opens M
参数：he : e in atlas H M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
Each chart of a charted space is a structomorphism between its source and target
.
-/
def OpenPartialHomeomorph.toStructomorph {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    [HasGroupoid M G] [ClosedUnderRestriction G] :
    let s : Opens M := { carrier := e.source, is_open' := e.open_source }
    let t : Opens H := { carrier := e.target, is_open' := e.open_target }
    Structomorph G s t := by
  intro s t
  by_cases! h : Nonempty e.source
  · exact { e.toHomeomorphSourceTarget with
      mem_groupoid :=
        -- The atlas of H on itself has only one chart, hence c' is the inclusion.
        -- Then, compatibility of `G` *almost* yields our claim --- except that `e` is a chart
        -- on `M` and `c` is one on `s`: we need to show that restricting `e` to `s` and composing
        -- with `c'` yields a chart in the maximal atlas of `s`.
        fun c c' hc hc' ↦ G.compatible_of_mem_maximalAtlas (G.subset_maximalAtlas hc)
          (G.restriction_mem_maximalAtlas_subtype he h c' hc') }
  · have : IsEmpty t := isEmpty_coe_sort.mpr
      (by convert! e.image_source_eq_target ▸ image_eq_empty.mpr (isEmpty_coe_sort.mp h))
    exact { Homeomorph.empty with
      -- `c'` cannot exist: it would be the restriction of `chartAt H x` at some `x ∈ t`.
      mem_groupoid := fun _ c' _ ⟨_, ⟨x, _⟩, _⟩ ↦ (this.false x).elim }

end HasGroupoid

