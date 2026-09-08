/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
/-!
# Partial homeomorphisms and continuity

## Main theorems

* `OpenPartialHomeomorph.map_nhds_eq`: an open partial homeomorphism preserves the neighbourhood
  filter of any point in its source.
* `OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left`,
  `OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_right`: a function is continuous at
  a point iff its pre / post composition with an open partial homeomorphism is so (assuming the
  point is in the source / target).
-/

public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-
**OpenPartialHomeomorph.eventually_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 `OpenP
artialHomeomorph`。
形式化陈述：eventually_left_inverse {x} (hx : x in e.source) : forallᶠ y in 𝓝 x, e.sym
m (e y) = y
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `PartialEquiv.left_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : PartialE
quiv α β) ⦃x : α⦄, x ∈ self.source → self.invFun (↑self x) = x
-/
theorem eventually_left_inverse {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'
/-
**OpenPartialHomeomorph.eventually_left_inverse'** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：eventually_left_inverse' {x} (hx : x in e.target) : forallᶠ y in 𝓝 (e.symm
 x), e.symm (e y) = y
参数：hx : x in e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.eventually_left_inverse`：eventually_left_inverse {
x} (hx : x in e.source) : forallᶠ y in 𝓝 x, e.symm (e y) = y
· 使用定理 `OpenPartialHomeomorph.map_target`：map_target {x : Y} (h : x in e.target)
 : e.symm x in e.source
-/
theorem eventually_left_inverse' {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)
/-
**OpenPartialHomeomorph.eventually_right_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：eventually_right_inverse {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e
.symm y) = y
参数：hx : x in e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `PartialEquiv.right_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : Partial
Equiv α β) ⦃x : β⦄, x ∈ self.target → ↑self (self.invFun x) = x
-/
theorem eventually_right_inverse {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'
/-
**OpenPartialHomeomorph.eventually_right_inverse'** 是 Mathlib 中的一个定理，位于命名空间 `Ope
nPartialHomeomorph`。
形式化陈述：eventually_right_inverse' {x} (hx : x in e.source) : forallᶠ y in 𝓝 (e x),
 e (e.symm y) = y
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse`：eventually_right_inverse
 {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e.symm y) = y
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
-/
theorem eventually_right_inverse' {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)
/-
**OpenPartialHomeomorph.eventually_ne_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：eventually_ne_nhdsWithin {x} (hx : x in e.source) : forallᶠ x' in 𝓝[!=] x,
 e x' != e x
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `OpenPartialHomeomorph.eventually_left_inverse`：eventually_left_inverse {
x} (hx : x in e.source) : forallᶠ y in 𝓝 x, e.symm (e y) = y
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
-/
theorem eventually_ne_nhdsWithin {x} (hx : x ∈ e.source) :
    ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhdsWithin_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']
/-
**OpenPartialHomeomorph.nhdsWithin_source_inter** 是 Mathlib 中的一个定理，位于命名空间 `OpenP
artialHomeomorph`。
形式化陈述：nhdsWithin_source_inter {x} (hx : x in e.source) (s : Set X) : 𝓝[e.source 
inter s] x = 𝓝[s] x
参数：hx : x in e.source；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem nhdsWithin_source_inter {x} (hx : x ∈ e.source) (s : Set X) : 𝓝[e.source ∩ s] x = 𝓝[s] x :=
  nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)
/-
**OpenPartialHomeomorph.nhdsWithin_target_inter** 是 Mathlib 中的一个定理，位于命名空间 `OpenP
artialHomeomorph`。
形式化陈述：nhdsWithin_target_inter {x} (hx : x in e.target) (s : Set Y) : 𝓝[e.target 
inter s] x = 𝓝[s] x
参数：hx : x in e.target；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.nhdsWithin_source_inter`：nhdsWithin_source_inter {
x} (hx : x in e.source) (s : Set X) : 𝓝[e.source inter s] x = 𝓝[s] x
-/
theorem nhdsWithin_target_inter {x} (hx : x ∈ e.target) (s : Set Y) : 𝓝[e.target ∩ s] x = 𝓝[s] x :=
  e.symm.nhdsWithin_source_inter hx s

/-- An open partial homeomorphism is continuous at any point of its source -/
/-
**OpenPartialHomeomorph.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y) {x : X}, x ∈ e.source → Contin
uousAt (↑e) x
参数：e : OpenPartialHomeomorph X Y；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.continuousAt`：ContinuousWithinAt.continuousAt (h : Co
ntinuousWithinAt f s x) (hs : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
An open partial homeomorphism is continuous at any point of its source
-/
protected theorem continuousAt {x : X} (h : x ∈ e.source) : ContinuousAt e x :=
  (e.continuousOn x h).continuousAt (e.open_source.mem_nhds h)

/-- An open partial homeomorphism inverse is continuous at any point of its target -/
/-
**OpenPartialHomeomorph.continuousAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartial
Homeomorph`。
形式化陈述：continuousAt_symm {x : Y} (h : x in e.target) : ContinuousAt e.symm x
参数：h : x in e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…

--- 原说明 ---
An open partial homeomorphism inverse is continuous at any point of its target
-/
theorem continuousAt_symm {x : Y} (h : x ∈ e.target) : ContinuousAt e.symm x :=
  e.symm.continuousAt h
/-
**OpenPartialHomeomorph.tendsto_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：tendsto_symm {x} (hx : x in e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x)
参数：hx : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `OpenPartialHomeomorph.continuousAt_symm`：continuousAt_symm {x : Y} (h : 
x in e.target) : ContinuousAt e.symm x
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
-/
theorem tendsto_symm {x} (hx : x ∈ e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuousAt_symm (e.map_source hx)
/-
**OpenPartialHomeomorph.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：map_nhds_eq {x} (hx : x in e.source) : map e (𝓝 x) = 𝓝 (e x)
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `Filter.le_map_of_right_inverse`：le_map_of_right_inverse {mab : α -> β} {
mba : β -> α} {f : Filter α} {g : Filter β} (h₁ : mab ∘ mba =ᶠ[g] id) (h₂ : Tend
sto mba g f) : g <= …
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse'`：eventually_right_invers
e' {x} (hx : x in e.source) : forallᶠ y in 𝓝 (e x), e (e.symm y) = y
· 使用定理 `OpenPartialHomeomorph.tendsto_symm`：tendsto_symm {x} (hx : x in e.source
) : Tendsto e.symm (𝓝 (e x)) (𝓝 x)
-/
theorem map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymm (e.continuousAt hx) <|
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)
/-
**OpenPartialHomeomorph.symm_map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：symm_map_nhds_eq {x} (hx : x in e.source) : map e.symm (𝓝 (e x)) = 𝓝 x
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OpenPartialHomeomorph.map_nhds_eq`：map_nhds_eq {x} (hx : x in e.source) 
: map e (𝓝 x) = 𝓝 (e x)
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
-/
theorem symm_map_nhds_eq {x} (hx : x ∈ e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by rw [e.left_inv hx]
/-
**OpenPartialHomeomorph.image_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph`。
形式化陈述：image_mem_nhds {x} (hx : x in e.source) {s : Set X} (hs : s in 𝓝 x) : e ''
 s in 𝓝 (e x)
参数：hx : x in e.source；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `OpenPartialHomeomorph.map_nhds_eq`：map_nhds_eq {x} (hx : x in e.source) 
: map e (𝓝 x) = 𝓝 (e x)
-/
theorem image_mem_nhds {x} (hx : x ∈ e.source) {s : Set X} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs
/-
**OpenPartialHomeomorph.map_nhdsWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartial
Homeomorph`。
形式化陈述：map_nhdsWithin_eq {x} (hx : x in e.source) (s : Set X) : map e (𝓝[s] x) = 
𝓝[e '' (e.source inter s)] e x
参数：hx : x in e.source；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.nhdsWithin_source_inter`：nhdsWithin_source_inter {
x} (hx : x in e.source) (s : Set X) : 𝓝[e.source inter s] x = 𝓝[s] x
· 使用定理 `Set.LeftInvOn.map_nhdsWithin_eq`：Set.LeftInvOn.map_nhdsWithin_eq {f : α 
-> β} {g : β -> α} {x : β} {s : Set β} (h : LeftInvOn f g s) (hx : f (g x) = x) 
(hf : ContinuousWithi…
· 使用定理 `Set.LeftInvOn.mono`：mono (hf : LeftInvOn f' f s) (ht : s₁ subseteq s) : 
LeftInvOn f' f s₁
· 使用定理 `OpenPartialHomeomorph.leftInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), Set.LeftInvOn (…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `OpenPartialHomeomorph.continuousAt_symm`：continuousAt_symm {x : Y} (h : 
x in e.target) : ContinuousAt e.symm x
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
-/
theorem map_nhdsWithin_eq {x} (hx : x ∈ e.source) (s : Set X) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source ∩ s)] e x :=
      (e.leftInvOn.mono inter_subset_left).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
        (e.continuousAt hx).continuousWithinAt
/-
**OpenPartialHomeomorph.map_nhdsWithin_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：map_nhdsWithin_preimage_eq {x} (hx : x in e.source) (s : Set Y) : map e (𝓝
[e ⁻¹' s] x) = 𝓝[s] e x
参数：hx : x in e.source；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.map_nhdsWithin_eq`：map_nhdsWithin_eq {x} (hx : x i
n e.source) (s : Set X) : map e (𝓝[s] x) = 𝓝[e '' (e.source inter s)] e x
· 使用定理 `OpenPartialHomeomorph.image_source_inter_eq'`：image_source_inter_eq' (s 
: Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `OpenPartialHomeomorph.target_inter_inv_preimage_preimage`：target_inter_i
nv_preimage_preimage (s : Set Y) : e.target inter e.symm ⁻¹' e ⁻¹' s = e.target 
inter s
· 使用定理 `OpenPartialHomeomorph.nhdsWithin_target_inter`：nhdsWithin_target_inter {
x} (hx : x in e.target) (s : Set Y) : 𝓝[e.target inter s] x = 𝓝[s] x
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
-/
theorem map_nhdsWithin_preimage_eq {x} (hx : x ∈ e.source) (s : Set Y) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhdsWithin_target_inter (e.map_source hx)]
/-
**OpenPartialHomeomorph.eventually_nhds** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：eventually_nhds {x : X} (p : Y -> Prop) (hx : x in e.source) : (forallᶠ y 
in 𝓝 (e x), p y) ↔ forallᶠ x in 𝓝 x, p (e x)
参数：p : Y -> Prop；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.map_nhds_eq`：map_nhds_eq {x} (hx : x in e.source) 
: map e (𝓝 x) = 𝓝 (e x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
-/
theorem eventually_nhds {x : X} (p : Y → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p y) ↔ ∀ᶠ x in 𝓝 x, p (e x) :=
  Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map
/-
**OpenPartialHomeomorph.eventually_nhds'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：eventually_nhds' {x : X} (p : X -> Prop) (hx : x in e.source) : (forallᶠ y
 in 𝓝 (e x), p (e.symm y)) ↔ forallᶠ x in 𝓝 x, p x
参数：p : X -> Prop；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.eventually_nhds`：eventually_nhds {x : X} (p : Y ->
 Prop) (hx : x in e.source) : (forallᶠ y in 𝓝 (e x), p y) ↔ forallᶠ x in 𝓝 x, p 
(e x)
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `OpenPartialHomeomorph.eventually_left_inverse`：eventually_left_inverse {
x} (hx : x in e.source) : forallᶠ y in 𝓝 x, e.symm (e y) = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_nhds' {x : X} (p : X → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p (e.symm y)) ↔ ∀ᶠ x in 𝓝 x, p x := by
  rw [e.eventually_nhds _ hx]
  refine eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => ?_)
  rw [hy]
/-
**OpenPartialHomeomorph.eventually_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：eventually_nhdsWithin {x : X} (p : Y -> Prop) {s : Set X} (hx : x in e.sou
rce) : (forallᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ forallᶠ x in 𝓝[s] x, p (e x)
参数：p : Y -> Prop；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.map_nhdsWithin_eq`：map_nhdsWithin_eq {x} (hx : x i
n e.source) (s : Set X) : map e (𝓝[s] x) = 𝓝[e '' (e.source inter s)] e x
· 使用定理 `OpenPartialHomeomorph.image_source_inter_eq'`：image_source_inter_eq' (s 
: Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `OpenPartialHomeomorph.nhdsWithin_target_inter`：nhdsWithin_target_inter {
x} (hx : x in e.target) (s : Set Y) : 𝓝[e.target inter s] x = 𝓝[s] x
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
-/
theorem eventually_nhdsWithin {x : X} (p : Y → Prop) {s : Set X}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ ∀ᶠ x in 𝓝[s] x, p (e x) := by
  refine Iff.trans ?_ eventually_map
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.nhdsWithin_target_inter (e.mapsTo hx)]
/-
**OpenPartialHomeomorph.eventually_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPa
rtialHomeomorph`。
形式化陈述：eventually_nhdsWithin' {x : X} (p : X -> Prop) {s : Set X} (hx : x in e.so
urce) : (forallᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ forallᶠ x in 𝓝[s] x, 
p x
参数：p : X -> Prop；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.eventually_nhdsWithin`：eventually_nhdsWithin {x : 
X} (p : Y -> Prop) {s : Set X} (hx : x in e.source) : (forallᶠ y in 𝓝[e.symm ⁻¹'
 s] e x, p y) ↔ forallᶠ x in 𝓝[s]…
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `OpenPartialHomeomorph.eventually_left_inverse`：eventually_left_inverse {
x} (hx : x in e.source) : forallᶠ y in 𝓝 x, e.symm (e y) = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_nhdsWithin' {x : X} (p : X → Prop) {s : Set X}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ ∀ᶠ x in 𝓝[s] x, p x := by
  rw [e.eventually_nhdsWithin _ hx]
  refine eventually_congr <|
    (eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy => ?_
  rw [hy]

/-- This lemma is useful in the manifold library in the case that `e` is a chart. It states that
  locally around `e x` the set `e.symm ⁻¹' s` is the same as the set intersected with the target
  of `e` and some other neighborhood of `f x` (which will be the source of a chart on `Z`). -/
/-
**OpenPartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter** 是 Ma
thlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：preimage_eventuallyEq_target_inter_preimage_inter {e : OpenPartialHomeomor
ph X Y} {s : Set X} {t : Set Z} {x : X} {f : X -> Z} (hf : ContinuousWithinAt f 
s x) (hxe : x in e.source) (ht : t in 𝓝 (f x)) : e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.tar
get inter e.symm ⁻¹' (s inter f ⁻¹' t) : Set Y)
参数：hf : ContinuousWithinAt f s x；hxe : x in e.source；ht : t in 𝓝 (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyEq_set`：eventuallyEq_set {s t : Set α} {l : Filter α} :
 s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t
· 使用定理 `OpenPartialHomeomorph.eventually_nhds`：eventually_nhds {x : X} (p : Y ->
 Prop) (hx : x in e.source) : (forallᶠ y in 𝓝 (e x), p y) ↔ forallᶠ x in 𝓝 x, p 
(e x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_eventually`：mem_nhdsWithin_iff_eventually {s t : Set 
α} {x : α} : t in 𝓝[s] x ↔ forallᶠ y in 𝓝 x, y in s -> y in t
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`：ContinuousWithinAt.preimage_
mem_nhdsWithin {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : 
f ⁻¹' t in 𝓝[s] x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)

--- 原说明 ---
This lemma is useful in the manifold library in the case that `e` is a chart. It
 states that
  locally around `e x` the set `e.symm ⁻¹' s` is the same as the set intersected
 with the target
  of `e` and some other neighborhood of `f x` (which will be the source of a cha
rt on `Z`).
-/
theorem preimage_eventuallyEq_target_inter_preimage_inter {e : OpenPartialHomeomorph X Y}
    {s : Set X} {t : Set Z} {x : X} {f : X → Z} (hf : ContinuousWithinAt f s x) (hxe : x ∈ e.source)
    (ht : t ∈ 𝓝 (f x)) :
    e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' t) : Set Y) := by
  rw [eventuallyEq_set, e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhdsWithin_iff_eventually.mp (hf.preimage_mem_nhdsWithin ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.mapsTo hy, true_and, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]

section Continuity

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
/-
**OpenPartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_right** 是
 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：continuousWithinAt_iff_continuousWithinAt_comp_right {f : Y -> Z} {s : Set
 Y} {x : Y} (h : x in e.target) : ContinuousWithinAt f s x ↔ ContinuousWithinAt 
(f ∘ e) (e ⁻¹' s) (e.symm x)
参数：h : x in e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.map_nhdsWithin_preimage_eq`：map_nhdsWithin_preimag
e_eq {x} (hx : x in e.source) (s : Set Y) : map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x
· 使用定理 `OpenPartialHomeomorph.map_target`：map_target {x : Y} (h : x in e.target)
 : e.symm x in e.source
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Continuity within a set at a point can be read under right composition with a lo
cal
homeomorphism, if the point is in its target
-/
theorem continuousWithinAt_iff_continuousWithinAt_comp_right {f : Y → Z} {s : Set Y} {x : Y}
    (h : x ∈ e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhdsWithin_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]

/-- Continuity at a point can be read under right composition with an open partial homeomorphism, if
the point is in its target -/
/-
**OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_right** 是 Mathlib 中的一
个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：continuousAt_iff_continuousAt_comp_right {f : Y -> Z} {x : Y} (h : x in e.
target) : ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x)
参数：h : x in e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `OpenPartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_rig
ht`：continuousWithinAt_iff_continuousWithinAt_comp_right {f : Y -> Z} {s : Set Y
} {x : Y} (h : x in e.target) : ContinuousWithinAt f s x ↔ Conti…
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Continuity at a point can be read under right composition with an open partial h
omeomorphism, if
the point is in its target
-/
theorem continuousAt_iff_continuousAt_comp_right {f : Y → Z} {x : Y} (h : x ∈ e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuousWithinAt_univ, e.continuousWithinAt_iff_continuousWithinAt_comp_right h,
    preimage_univ, continuousWithinAt_univ]

/-- A function is continuous on a set if and only if its composition with an open partial
homeomorphism on the right is continuous on the corresponding set. -/
/-
**OpenPartialHomeomorph.continuousOn_iff_continuousOn_comp_right** 是 Mathlib 中的一
个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：continuousOn_iff_continuousOn_comp_right {f : Y -> Z} {s : Set Y} (h : s s
ubseteq e.target) : ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source inter e ⁻¹
' s)
参数：h : s subseteq e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.symm_image_eq_source_inter_preimage`：symm_image_eq
_source_inter_preimage {s : Set Y} (h : s subseteq e.target) : e.symm '' s = e.s
ource inter e ⁻¹' s
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `OpenPartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_rig
ht`：continuousWithinAt_iff_continuousWithinAt_comp_right {f : Y -> Z} {s : Set Y
} {x : Y} (h : x in e.target) : ContinuousWithinAt f s x ↔ Conti…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `continuousWithinAt_inter`：continuousWithinAt_inter (h : t in 𝓝 x) : Cont
inuousWithinAt f (s inter t) x ↔ ContinuousWithinAt f s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.map_target`：map_target {x : Y} (h : x in e.target)
 : e.symm x in e.source
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A function is continuous on a set if and only if its composition with an open pa
rtial
homeomorphism on the right is continuous on the corresponding set.
-/
theorem continuousOn_iff_continuousOn_comp_right {f : Y → Z} {s : Set Y} (h : s ⊆ e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source ∩ e ⁻¹' s) := by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right (h hx),
    e.symm_image_eq_source_inter_preimage h, inter_comm, continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism -/
/-
**OpenPartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_left** 是 
Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：continuousWithinAt_iff_continuousWithinAt_comp_left {f : Z -> X} {s : Set 
Z} {x : Z} (hx : f x in e.source) (h : f ⁻¹' e.source in 𝓝[s] x) : ContinuousWit
hinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x
参数：hx : f x in e.source；h : f ⁻¹' e.source in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_inter'`：continuousWithinAt_inter' (h : t in 𝓝[s] x) :
 ContinuousWithinAt f (s inter t) x ↔ ContinuousWithinAt f s x
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `OpenPartialHomeomorph.continuousAt_symm`：continuousAt_symm {x : Y} (h : 
x in e.target) : ContinuousAt e.symm x
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Continuity within a set at a point can be read under left composition with a loc
al
homeomorphism if a neighborhood of the initial point is sent to the source of th
e local
homeomorphism
-/
theorem continuousWithinAt_iff_continuousWithinAt_comp_left {f : Z → X} {s : Set Z} {x : Z}
    (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x := by
  refine ⟨(e.continuousAt hx).comp_continuousWithinAt, fun fe_cont => ?_⟩
  rw [← continuousWithinAt_inter' h] at fe_cont ⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])

/-- Continuity at a point can be read under left composition with an open partial homeomorphism if a
neighborhood of the initial point is sent to the source of the partial homeomorphism -/
/-
**OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left** 是 Mathlib 中的一个
定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：continuousAt_iff_continuousAt_comp_left {f : Z -> X} {x : Z} (h : f ⁻¹' e.
source in 𝓝 x) : ContinuousAt f x ↔ ContinuousAt (e ∘ f) x
参数：h : f ⁻¹' e.source in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `OpenPartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_lef
t`：continuousWithinAt_iff_continuousWithinAt_comp_left {f : Z -> X} {s : Set Z} 
{x : Z} (hx : f x in e.source) (h : f ⁻¹' e.source in 𝓝[s] x) :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Continuity at a point can be read under left composition with an open partial ho
meomorphism if a
neighborhood of the initial point is sent to the source of the partial homeomorp
hism
-/
theorem continuousAt_iff_continuousAt_comp_left {f : Z → X} {x : Z} (h : f ⁻¹' e.source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x := by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h :)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ, ← continuousWithinAt_univ,
    e.continuousWithinAt_iff_continuousWithinAt_comp_left hx h']

/-- A function is continuous on a set if and only if its composition with an open partial
homeomorphism on the left is continuous on the corresponding set. -/
/-
**OpenPartialHomeomorph.continuousOn_iff_continuousOn_comp_left** 是 Mathlib 中的一个
定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：continuousOn_iff_continuousOn_comp_left {f : Z -> X} {s : Set Z} (h : s su
bseteq f ⁻¹' e.source) : ContinuousOn f s ↔ ContinuousOn (e ∘ f) s
参数：h : s subseteq f ⁻¹' e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `OpenPartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_lef
t`：continuousWithinAt_iff_continuousWithinAt_comp_left {f : Z -> X} {s : Set Z} 
{x : Z} (hx : f x in e.source) (h : f ⁻¹' e.source in 𝓝[s] x) :…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
A function is continuous on a set if and only if its composition with an open pa
rtial
homeomorphism on the left is continuous on the corresponding set.
-/
theorem continuousOn_iff_continuousOn_comp_left {f : Z → X} {s : Set Z} (h : s ⊆ f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congr fun _x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)

/-- A function is continuous if and only if its composition with an open partial homeomorphism
on the left is continuous and its image is contained in the source. -/
/-
**OpenPartialHomeomorph.continuous_iff_continuous_comp_left** 是 Mathlib 中的一个定理，位
于命名空间 `OpenPartialHomeomorph`。
形式化陈述：continuous_iff_continuous_comp_left {f : Z -> X} (h : f ⁻¹' e.source = uni
v) : Continuous f ↔ Continuous (e ∘ f)
参数：h : f ⁻¹' e.source = univ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.continuousOn_iff_continuousOn_comp_left`：continuou
sOn_iff_continuousOn_comp_left {f : Z -> X} {s : Set Z} (h : s subseteq f ⁻¹' e.
source) : ContinuousOn f s ↔ ContinuousOn (e ∘ f) s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A function is continuous if and only if its composition with an open partial hom
eomorphism
on the left is continuous and its image is contained in the source.
-/
theorem continuous_iff_continuous_comp_left {f : Z → X} (h : f ⁻¹' e.source = univ) :
    Continuous f ↔ Continuous (e ∘ f) := by
  simp only [← continuousOn_univ]
  exact e.continuousOn_iff_continuousOn_comp_left (Eq.symm h).subset

end Continuity

end OpenPartialHomeomorph

