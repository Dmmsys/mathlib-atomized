/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Maps.Basic

/-!
# Open quotient maps

An open quotient map is an open map `f : X → Y` which is both an open map and a quotient map.
Equivalently, it is a surjective continuous open map.
We use the latter characterization as a definition.

Many important quotient maps are open quotient maps, including

- the quotient map from a topological space to its quotient by the action of a group;
- the quotient map from a topological group to its quotient by a normal subgroup;
- the quotient map from a topological space to its separation quotient.

Contrary to general quotient maps,
the category of open quotient maps is closed under `Prod.map`.
-/

public section

open Filter Function Set Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y}

namespace IsOpenQuotientMap

/-
**IsOpenQuotientMap.id** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotientMap`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenQuotientMap id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
-/
protected theorem id : IsOpenQuotientMap (id : X → X) := ⟨surjective_id, continuous_id, .id⟩

/-- An open quotient map is a quotient map. -/
/-
**IsOpenQuotientMap.isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotientMap`。
形式化陈述：isQuotientMap (h : IsOpenQuotientMap f) : IsQuotientMap f
参数：h : IsOpenQuotientMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → Continuo
us f → Functi…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…

--- 原说明 ---
An open quotient map is a quotient map.
-/
theorem isQuotientMap (h : IsOpenQuotientMap f) : IsQuotientMap f :=
  h.isOpenMap.isQuotientMap h.continuous h.surjective
/-
**IsOpenQuotientMap.iff_isOpenMap_isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `IsOpe
nQuotientMap`。
形式化陈述：iff_isOpenMap_isQuotientMap : IsOpenQuotientMap f ↔ IsOpenMap f ∧ IsQuotie
ntMap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `Topology.IsQuotientMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : 
X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsQ
uotientMap f → Continuo…
-/
theorem iff_isOpenMap_isQuotientMap : IsOpenQuotientMap f ↔ IsOpenMap f ∧ IsQuotientMap f :=
  ⟨fun h ↦ ⟨h.isOpenMap, h.isQuotientMap⟩, fun ⟨ho, hq⟩ ↦ ⟨hq.surjective, hq.continuous, ho⟩⟩
/-
**IsOpenQuotientMap.of_isOpenMap_isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen
QuotientMap`。
形式化陈述：of_isOpenMap_isQuotientMap (ho : IsOpenMap f) (hq : IsQuotientMap f) : IsO
penQuotientMap f
参数：ho : IsOpenMap f；hq : IsQuotientMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpenQuotientMap.iff_isOpenMap_isQuotientMap`：iff_isOpenMap_isQuotientM
ap : IsOpenQuotientMap f ↔ IsOpenMap f ∧ IsQuotientMap f
-/
theorem of_isOpenMap_isQuotientMap (ho : IsOpenMap f) (hq : IsQuotientMap f) :
    IsOpenQuotientMap f :=
  iff_isOpenMap_isQuotientMap.2 ⟨ho, hq⟩
/-
**IsOpenQuotientMap.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotientMap`。
形式化陈述：comp {g : Y -> Z} (hg : IsOpenQuotientMap g) (hf : IsOpenQuotientMap f) : 
IsOpenQuotientMap (g ∘ f)
参数：hg : IsOpenQuotientMap g；hf : IsOpenQuotientMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
-/
theorem comp {g : Y → Z} (hg : IsOpenQuotientMap g) (hf : IsOpenQuotientMap f) :
    IsOpenQuotientMap (g ∘ f) :=
  ⟨.comp hg.1 hf.1, .comp hg.2 hf.2, .comp hg.3 hf.3⟩
/-
**IsOpenQuotientMap.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotientMap`。
形式化陈述：of_comp {g : Y -> Z} (hf : Continuous f) (f_surj : Surjective f) (hg : Con
tinuous g) (h : IsOpenQuotientMap (g ∘ f)) : IsOpenQuotientMap g
参数：hf : Continuous f；f_surj : Surjective f；hg : Continuous g；h : IsOpenQuotientM
ap (g ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `IsOpenMap.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X
 → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [i
nst_2 :…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
-/
theorem of_comp {g : Y → Z} (hf : Continuous f) (f_surj : Surjective f) (hg : Continuous g)
    (h : IsOpenQuotientMap (g ∘ f)) : IsOpenQuotientMap g :=
  ⟨.of_comp h.surjective, hg, .of_comp hf f_surj h.isOpenMap ⟩
/-
**IsOpenQuotientMap.of_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotientMap`。
形式化陈述：of_comp_iff {g : Y -> Z} (hf : IsOpenQuotientMap f) : IsOpenQuotientMap (g
 ∘ f) ↔ IsOpenQuotientMap g
参数：hf : IsOpenQuotientMap f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.of_comp`：of_comp {g : Y -> Z} (hf : Continuous f) (f_s
urj : Surjective f) (hg : Continuous g) (h : IsOpenQuotientMap (g ∘ f)) : IsOpen
QuotientMap g
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `IsOpenQuotientMap.comp`：comp {g : Y -> Z} (hg : IsOpenQuotientMap g) (hf
 : IsOpenQuotientMap f) : IsOpenQuotientMap (g ∘ f)
-/
theorem of_comp_iff {g : Y → Z} (hf : IsOpenQuotientMap f) :
    IsOpenQuotientMap (g ∘ f) ↔ IsOpenQuotientMap g :=
  ⟨fun h ↦ .of_comp hf.continuous hf.surjective
    (hf.isQuotientMap.continuous_iff.mpr h.continuous) h, fun hg ↦ hg.comp hf⟩
/-
**IsOpenQuotientMap.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotientMap`。
形式化陈述：map_nhds_eq (h : IsOpenQuotientMap f) (x : X) : map f (𝓝 x) = 𝓝 (f x)
参数：h : IsOpenQuotientMap f；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenMap.nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → ∀ (x : X), nhd
s (f x)…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
-/
theorem map_nhds_eq (h : IsOpenQuotientMap f) (x : X) : map f (𝓝 x) = 𝓝 (f x) :=
  le_antisymm h.continuous.continuousAt <| h.isOpenMap.nhds_le _
/-
**IsOpenQuotientMap.continuous_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotien
tMap`。
形式化陈述：continuous_comp_iff (h : IsOpenQuotientMap f) {g : Y -> Z} : Continuous (g
 ∘ f) ↔ Continuous g
参数：h : IsOpenQuotientMap f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
-/
theorem continuous_comp_iff (h : IsOpenQuotientMap f) {g : Y → Z} :
    Continuous (g ∘ f) ↔ Continuous g :=
  h.isQuotientMap.continuous_iff.symm
/-
**IsOpenQuotientMap.continuousAt_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuoti
entMap`。
形式化陈述：continuousAt_comp_iff (h : IsOpenQuotientMap f) {g : Y -> Z} {x : X} : Con
tinuousAt (g ∘ f) x ↔ ContinuousAt g (f x)
参数：h : IsOpenQuotientMap f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenQuotientMap.map_nhds_eq`：map_nhds_eq (h : IsOpenQuotientMap f) (x 
: X) : map f (𝓝 x) = 𝓝 (f x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_comp_iff (h : IsOpenQuotientMap f) {g : Y → Z} {x : X} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp only [ContinuousAt, ← h.map_nhds_eq, tendsto_map'_iff, comp_def]
/-
**IsOpenQuotientMap.isOpenMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotientMap`。
形式化陈述：isOpenMap_iff (hf : IsOpenQuotientMap f) {g : Y -> Z} : IsOpenMap g ↔ IsOp
enMap (g ∘ f)
参数：hf : IsOpenQuotientMap f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
· 使用定理 `IsOpenMap.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X
 → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [i
nst_2 :…
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
-/
theorem isOpenMap_iff (hf : IsOpenQuotientMap f) {g : Y → Z} :
    IsOpenMap g ↔ IsOpenMap (g ∘ f) :=
  ⟨fun hg ↦ hg.comp hf.isOpenMap, fun h ↦ .of_comp hf.continuous hf.surjective h⟩
/-
**IsOpenQuotientMap.dense_preimage_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsOpenQuotient
Map`。
形式化陈述：dense_preimage_iff (h : IsOpenQuotientMap f) {s : Set Y} : Dense (f ⁻¹' s)
 ↔ Dense s
参数：h : IsOpenQuotientMap f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.dense_of_mapsTo`：DenseRange.dense_of_mapsTo {f : X -> Y} (hf'
 : DenseRange f) (hf : Continuous f) (hs : Dense s) {t : Set Y} (ht : MapsTo f s
 t) : Dense t
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Dense.preimage`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] {s : Set Y},   Dense s → IsOpenMap
 f →…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
-/
theorem dense_preimage_iff (h : IsOpenQuotientMap f) {s : Set Y} : Dense (f ⁻¹' s) ↔ Dense s :=
  ⟨fun hs ↦ h.surjective.denseRange.dense_of_mapsTo h.continuous hs (mapsTo_preimage _ _),
    fun hs ↦ hs.preimage h.isOpenMap⟩

end IsOpenQuotientMap

/-
**Topology.IsInducing.isOpenQuotientMap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Topology.IsInducing.isOpenQuotientMap_of_surjective (ind : IsInducing f) (
surj : Function.Surjective f) : IsOpenQuotientMap f where surjective
参数：ind : IsInducing f；surj : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
-/
theorem Topology.IsInducing.isOpenQuotientMap_of_surjective (ind : IsInducing f)
    (surj : Function.Surjective f) : IsOpenQuotientMap f where
  surjective := surj
  continuous := ind.continuous
  isOpenMap U U_open := by
    obtain ⟨V, hV, rfl⟩ := ind.isOpen_iff.mp U_open
    rwa [V.image_preimage_eq surj]
/-
**Topology.IsInducing.isQuotientMap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isQuotientMap_of_surjective (ind : IsInducing f) (surj
 : Function.Surjective f) : IsQuotientMap f
参数：ind : IsInducing f；surj : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `Topology.IsInducing.isOpenQuotientMap_of_surjective`：Topology.IsInducing
.isOpenQuotientMap_of_surjective (ind : IsInducing f) (surj : Function.Surjectiv
e f) : IsOpenQuotientMap f where surjecti…
-/
theorem Topology.IsInducing.isQuotientMap_of_surjective (ind : IsInducing f)
    (surj : Function.Surjective f) : IsQuotientMap f :=
  (ind.isOpenQuotientMap_of_surjective surj).isQuotientMap

section Subquotient

variable {A B C D : Type*}
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
variable (f : A → B) (g : C → D) (p : A → C) (q : B → D)

omit [TopologicalSpace C] in
/--
Given the following diagram with `f` inducing, `p` surjective,
`q` an open quotient map, and `g` injective. Suppose the image of `A` in `B` is stable
under the equivalence mod `q`, then the coinduced topology on `C` (from `A`)
coincides with the induced topology (from `D`).
```
A -f→ B
∣     ∣
p     q
↓     ↓
C -g→ D
```

A typical application is when `K ≤ H` are subgroups of `G`, then the quotient topology on `H/K`
is also the subspace topology from `G/K`.
-/
/-
**coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing (h : g ∘ p = q ∘ f
) (hf : IsInducing f) (hp : Function.Surjective p) (hq : IsOpenQuotientMap q) (h
g : Function.Injective g) (H : q ⁻¹' q '' Set.range f subseteq Set.range f) : ‹T
opologicalSpace A›.coinduced p = ‹TopologicalSpace D›.induced g
参数：h : g ∘ p = q ∘ f；hf : IsInducing f；hp : Function.Surjective p；hq : IsOpenQuo
tientMap q；hg : Function.Injective g；H : q ⁻¹' q '' Set.range f subseteq Set.ran
ge f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_surjective`：image_surjective : Surjective (image f) ↔ Surjecti
ve f
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given the following diagram with `f` inducing, `p` surjective,
`q` an open quotient map, and `g` injective. Suppose the image of `A` in `B` is 
stable
under the equivalence mod `q`, then the coinduced topology on `C` (from `A`)
coincides with the induced topology (from `D`).
```
A -f→ B
∣     ∣
p     q
↓     ↓
C -g→ D
```

A typical application is when `K ≤ H` are subgroups of `G`, then the quotient to
pology on `H/K`
is also the subspace topology from `G/K`.
-/
lemma coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    (h : g ∘ p = q ∘ f)
    (hf : IsInducing f) (hp : Function.Surjective p)
    (hq : IsOpenQuotientMap q) (hg : Function.Injective g)
    (H : q ⁻¹' q '' Set.range f ⊆ Set.range f) :
    ‹TopologicalSpace A›.coinduced p = ‹TopologicalSpace D›.induced g := by
  ext U
  change IsOpen (p ⁻¹' U) ↔ ∃ V, _
  simp_rw [hf.isOpen_iff,
    (Set.image_surjective.mpr hq.surjective).exists,
    ← hq.isQuotientMap.isOpen_preimage]
  constructor
  · rintro ⟨V, hV, e⟩
    refine ⟨V, hq.continuous.1 _ (hq.isOpenMap _ hV), ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := hp x
    constructor
    · rintro ⟨y, hy, e'⟩
      obtain ⟨y, rfl⟩ := H ⟨_, ⟨x, rfl⟩, (e'.trans (congr_fun h x)).symm⟩
      rw [← hg ((congr_fun h y).trans e')]
      exact e.le hy
    · intro H
      exact ⟨f x, e.ge H, congr_fun h.symm x⟩
  · rintro ⟨V, hV, rfl⟩
    refine ⟨_, hV, ?_⟩
    simp_rw [← Set.preimage_comp, h]
/-
**isEmbedding_of_isOpenQuotientMap_of_isInducing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isEmbedding_of_isOpenQuotientMap_of_isInducing (h : g ∘ p = q ∘ f) (hf : I
sInducing f) (hp : IsQuotientMap p) (hq : IsOpenQuotientMap q) (hg : Function.In
jective g) (H : q ⁻¹' q '' Set.range f subseteq Set.range f) : IsEmbedding g
参数：h : g ∘ p = q ∘ f；hf : IsInducing f；hp : IsQuotientMap p；hq : IsOpenQuotientM
ap q；hg : Function.Injective g；H : q ⁻¹' q '' Set.range f subseteq Set.range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Topology.IsCoinducing.eq_coinduced`：∀ {X : Type u_1} {Y : Type u_2} [tX 
: TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsCoindu
cing f → tY = Topologica…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用引理 `coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing`：coinduced_eq_in
duced_of_isOpenQuotientMap_of_isInducing (h : g ∘ p = q ∘ f) (hf : IsInducing f)
 (hp : Function.Surjective p) (hq : IsOpenQuo…
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
-/
lemma isEmbedding_of_isOpenQuotientMap_of_isInducing
    (h : g ∘ p = q ∘ f)
    (hf : IsInducing f) (hp : IsQuotientMap p)
    (hq : IsOpenQuotientMap q) (hg : Function.Injective g)
    (H : q ⁻¹' q '' Set.range f ⊆ Set.range f) :
    IsEmbedding g :=
  ⟨⟨hp.eq_coinduced.trans (coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp.surjective hq hg H)⟩, hg⟩
/-
**isQuotientMap_of_isOpenQuotientMap_of_isInducing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isQuotientMap_of_isOpenQuotientMap_of_isInducing (h : g ∘ p = q ∘ f) (hf :
 IsInducing f) (hp : Surjective p) (hq : IsOpenQuotientMap q) (hg : IsEmbedding 
g) (H : q ⁻¹' q '' Set.range f subseteq Set.range f) : IsQuotientMap p
参数：h : g ∘ p = q ∘ f；hf : IsInducing f；hp : Surjective p；hq : IsOpenQuotientMap 
q；hg : IsEmbedding g；H : q ⁻¹' q '' Set.range f subseteq Set.range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing`：coinduced_eq_in
duced_of_isOpenQuotientMap_of_isInducing (h : g ∘ p = q ∘ f) (hf : IsInducing f)
 (hp : Function.Surjective p) (hq : IsOpenQuo…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
lemma isQuotientMap_of_isOpenQuotientMap_of_isInducing
    (h : g ∘ p = q ∘ f)
    (hf : IsInducing f) (hp : Surjective p)
    (hq : IsOpenQuotientMap q) (hg : IsEmbedding g)
    (H : q ⁻¹' q '' Set.range f ⊆ Set.range f) :
    IsQuotientMap p :=
  ⟨⟨hg.eq_induced.trans ((coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp hq hg.injective H)).symm⟩, hp⟩

end Subquotient

