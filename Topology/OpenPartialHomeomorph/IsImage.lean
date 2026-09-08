/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
/-!
# Partial homeomorphisms: Images of sets

## Main definitions

* `OpenPartialHomeomorph.IsImage`: predicate for when one set is an image of another
* `OpenPartialHomeomorph.ofSet`: the identity on a set `s`
* `OpenPartialHomeomorph.EqOnSource`: equivalence relation describing the "right" notion of equality
  for open partial homeomorphisms

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `PartialEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

section IsImage

/-!
## `OpenPartialHomeomorph.IsImage` relation

We say that `t : Set Y` is an image of `s : Set X` under an open partial homeomorphism `e` if any of
the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `PartialEquiv.IsImage` for open partial homeomorphisms.
In this section we transfer API about `PartialEquiv.IsImage` to open partial homeomorphisms and
add a few `OpenPartialHomeomorph`-specific lemmas like `OpenPartialHomeomorph.IsImage.closure`.
-/

/-- We say that `t : Set Y` is an image of `s : Set X` under an open partial homeomorphism `e`
if any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
/-
**OpenPartialHomeomorph.IsImage** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph
`。
形式化陈述：IsImage (s : Set X) (t : Set Y) : Prop
参数：s : Set X；t : Set Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `t : Set Y` is an image of `s : Set X` under an open partial homeomo
rphism `e`
if any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set X) (t : Set Y) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set X} {t : Set Y} {x : X} {y : Y}

/-
**OpenPartialHomeomorph.IsImage.toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OpenPa
rtialHomeomorph.IsImage`。
形式化陈述：toPartialEquiv (h : e.IsImage s t) : e.toPartialEquiv.IsImage s t
参数：h : e.IsImage s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPartialEquiv (h : e.IsImage s t) : e.toPartialEquiv.IsImage s t :=
  h
/-
**OpenPartialHomeomorph.IsImage.apply_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph.IsImage`。
形式化陈述：apply_mem_iff (h : e.IsImage s t) (hx : x in e.source) : e x in t ↔ x in s
参数：h : e.IsImage s t；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
/-
**OpenPartialHomeomorph.IsImage.symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph.IsImage`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y}, e.IsI
mage s t → e.symm.IsImage t s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.symm`：∀ {α : Type u_1} {β : Type u_2} {e : PartialE
quiv α β} {s : Set α} {t : Set β}, e.IsImage s t → e.symm.IsImage t s
· 使用定理 `OpenPartialHomeomorph.IsImage.toPartialEquiv`：toPartialEquiv (h : e.IsIm
age s t) : e.toPartialEquiv.IsImage s t
-/
protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toPartialEquiv.symm
/-
**OpenPartialHomeomorph.IsImage.symm_apply_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph.IsImage`。
形式化陈述：symm_apply_mem_iff (h : e.IsImage s t) (hy : y in e.target) : e.symm y in 
s ↔ y in t
参数：h : e.IsImage s t；hy : y in e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.symm`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeomor
ph X Y} {s : Set X} {t :…
-/
theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy

@[simp]
/-
**OpenPartialHomeomorph.IsImage.symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph.IsImage`。
形式化陈述：symm_iff : e.symm.IsImage t s ↔ e.IsImage s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.symm`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeomor
ph X Y} {s : Set X} {t :…
-/
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
/-
**OpenPartialHomeomorph.IsImage.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph.IsImage`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y}, e.IsI
mage s t → Set.MapsTo (↑e) (e.source ∩ s) (e.target ∩ t)
参数：↑e；e.source ∩ s；e.target ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {e : Partia
lEquiv α β} {s : Set α} {t : Set β},   e.IsImage s t → Set.MapsTo (↑e) (e.source
 ∩ s) (e.target ∩…
· 使用定理 `OpenPartialHomeomorph.IsImage.toPartialEquiv`：toPartialEquiv (h : e.IsIm
age s t) : e.toPartialEquiv.IsImage s t
-/
protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toPartialEquiv.mapsTo
/-
**OpenPartialHomeomorph.IsImage.symm_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `OpenParti
alHomeomorph.IsImage`。
形式化陈述：symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target inter t) (e.sour
ce inter s)
参数：h : e.IsImage s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeom
orph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.symm`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeomor
ph X Y} {s : Set X} {t :…
-/
theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo
/-
**OpenPartialHomeomorph.IsImage.image_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph.IsImage`。
形式化陈述：image_eq (h : e.IsImage s t) : e '' (e.source inter s) = e.target inter t
参数：h : e.IsImage s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.image_eq`：image_eq (h : e.IsImage s t) : e '' (e.so
urce inter s) = e.target inter t
· 使用定理 `OpenPartialHomeomorph.IsImage.toPartialEquiv`：toPartialEquiv (h : e.IsIm
age s t) : e.toPartialEquiv.IsImage s t
-/
theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toPartialEquiv.image_eq
/-
**OpenPartialHomeomorph.IsImage.symm_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph.IsImage`。
形式化陈述：symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target inter t) = e.sourc
e inter s
参数：h : e.IsImage s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.image_eq`：image_eq (h : e.IsImage s t) : e
 '' (e.source inter s) = e.target inter t
· 使用定理 `OpenPartialHomeomorph.IsImage.symm`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeomor
ph X Y} {s : Set X} {t :…
-/
theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
/-
**OpenPartialHomeomorph.IsImage.iff_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenP
artialHomeomorph.IsImage`。
形式化陈述：iff_preimage_eq : e.IsImage s t ↔ e.source inter e ⁻¹' t = e.source inter 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.iff_preimage_eq`：iff_preimage_eq : e.IsImage s t ↔ 
e.source inter e ⁻¹' t = e.source inter s
-/
theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  PartialEquiv.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq
/-
**OpenPartialHomeomorph.IsImage.iff_symm_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `
OpenPartialHomeomorph.IsImage`。
形式化陈述：iff_symm_preimage_eq : e.IsImage s t ↔ e.target inter e.symm ⁻¹' s = e.tar
get inter t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `OpenPartialHomeomorph.IsImage.symm_iff`：symm_iff : e.symm.IsImage t s ↔ 
e.IsImage s t
· 使用定理 `OpenPartialHomeomorph.IsImage.iff_preimage_eq`：iff_preimage_eq : e.IsIma
ge s t ↔ e.source inter e ⁻¹' t = e.source inter s
-/
theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq
/-
**OpenPartialHomeomorph.IsImage.iff_symm_preimage_eq'** 是 Mathlib 中的一个定理，位于命名空间 
`OpenPartialHomeomorph.IsImage`。
形式化陈述：iff_symm_preimage_eq' : e.IsImage s t ↔ e.target inter e.symm ⁻¹' (e.sourc
e inter s) = e.target inter t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.IsImage.iff_symm_preimage_eq`：iff_symm_preimage_eq
 : e.IsImage s t ↔ e.target inter e.symm ⁻¹' s = e.target inter t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.image_source_inter_eq`：image_source_inter_eq (s : 
Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' (e.source inter s)
· 使用定理 `OpenPartialHomeomorph.image_source_inter_eq'`：image_source_inter_eq' (s 
: Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'
/-
**OpenPartialHomeomorph.IsImage.iff_preimage_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph.IsImage`。
形式化陈述：iff_preimage_eq' : e.IsImage s t ↔ e.source inter e ⁻¹' (e.target inter t)
 = e.source inter s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `OpenPartialHomeomorph.IsImage.symm_iff`：symm_iff : e.symm.IsImage t s ↔ 
e.IsImage s t
· 使用定理 `OpenPartialHomeomorph.IsImage.iff_symm_preimage_eq'`：iff_symm_preimage_e
q' : e.IsImage s t ↔ e.target inter e.symm ⁻¹' (e.source inter s) = e.target int
er t
-/
theorem iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'
/-
**OpenPartialHomeomorph.IsImage.of_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenParti
alHomeomorph.IsImage`。
形式化陈述：of_image_eq (h : e '' (e.source inter s) = e.target inter t) : e.IsImage s
 t
参数：h : e '' (e.source inter s) = e.target inter t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.of_image_eq`：of_image_eq (h : e '' (e.source inter 
s) = e.target inter t) : e.IsImage s t
-/
theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  PartialEquiv.IsImage.of_image_eq h
/-
**OpenPartialHomeomorph.IsImage.of_symm_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph.IsImage`。
形式化陈述：of_symm_image_eq (h : e.symm '' (e.target inter t) = e.source inter s) : e
.IsImage s t
参数：h : e.symm '' (e.target inter t) = e.source inter s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.of_symm_image_eq`：of_symm_image_eq (h : e.symm '' (
e.target inter t) = e.source inter s) : e.IsImage s t
-/
theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  PartialEquiv.IsImage.of_symm_image_eq h
/-
**OpenPartialHomeomorph.IsImage.compl** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph.IsImage`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y}, e.IsI
mage s t → e.IsImage sᶜ tᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => (h hx).not
/-
**OpenPartialHomeomorph.IsImage.inter** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph.IsImage`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y} {s' : 
Set X} {t' : Set Y},   e.IsImage s t → e.IsImage s' t' → e.IsImage (s ∩ s') (t ∩
 t')
参数：s ∩ s'；t ∩ t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
-/
protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => (h hx).and (h' hx)
/-
**OpenPartialHomeomorph.IsImage.union** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph.IsImage`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y} {s' : 
Set X} {t' : Set Y},   e.IsImage s t → e.IsImage s' t' → e.IsImage (s ∪ s') (t ∪
 t')
参数：s ∪ s'；t ∪ t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.or`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
-/
protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => (h hx).or (h' hx)
/-
**OpenPartialHomeomorph.IsImage.diff** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph.IsImage`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y} {s' : 
Set X} {t' : Set Y},   e.IsImage s t → e.IsImage s' t' → e.IsImage (s \ s') (t \
 t')
参数：s \ s'；t \ t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.inter`：∀ {X : Type u_1} {Y : Type u_3} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeomo
rph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.compl`：∀ {X : Type u_1} {Y : Type u_3} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeomo
rph X Y} {s : Set X} {t :…
-/
protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
/-
**OpenPartialHomeomorph.IsImage.leftInvOn_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `O
penPartialHomeomorph.IsImage`。
形式化陈述：leftInvOn_piecewise {e' : OpenPartialHomeomorph X Y} [forall i, Decidable 
(i in s)] [forall i, Decidable (i in t)] (h : e.IsImage s t) (h' : e'.IsImage s 
t) : LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e
'.source)
参数：i in s；i in t；h : e.IsImage s t；h' : e'.IsImage s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.leftInvOn_piecewise`：leftInvOn_piecewise {e' : Part
ialEquiv α β} [forall i, Decidable (i in s)] [forall i, Decidable (i in t)] (h :
 e.IsImage s t) (h' : e'.IsIma…
· 使用定理 `OpenPartialHomeomorph.IsImage.toPartialEquiv`：toPartialEquiv (h : e.IsIm
age s t) : e.toPartialEquiv.IsImage s t
-/
theorem leftInvOn_piecewise {e' : OpenPartialHomeomorph X Y} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toPartialEquiv.leftInvOn_piecewise h'
/-
**OpenPartialHomeomorph.IsImage.inter_eq_of_inter_eq_of_eqOn** 是 Mathlib 中的一个定理，
位于命名空间 `OpenPartialHomeomorph.IsImage`。
形式化陈述：inter_eq_of_inter_eq_of_eqOn {e' : OpenPartialHomeomorph X Y} (h : e.IsIma
ge s t) (h' : e'.IsImage s t) (hs : e.source inter s = e'.source inter s) (Heq :
 EqOn e e' (e.source inter s)) : e.target inter t = e'.target inter t
参数：h : e.IsImage s t；h' : e'.IsImage s t；hs : e.source inter s = e'.source inter
 s；Heq : EqOn e e' (e.source inter s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn`：inter_eq_of_inter_eq_
of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t) (h' : e'.IsImage s t) (hs : 
e.source inter s = e'.source inter s) (…
· 使用定理 `OpenPartialHomeomorph.IsImage.toPartialEquiv`：toPartialEquiv (h : e.IsIm
age s t) : e.toPartialEquiv.IsImage s t
-/
theorem inter_eq_of_inter_eq_of_eqOn {e' : OpenPartialHomeomorph X Y} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq
/-
**OpenPartialHomeomorph.IsImage.symm_eqOn_of_inter_eq_of_eqOn** 是 Mathlib 中的一个定理
，位于命名空间 `OpenPartialHomeomorph.IsImage`。
形式化陈述：symm_eqOn_of_inter_eq_of_eqOn {e' : OpenPartialHomeomorph X Y} (h : e.IsIm
age s t) (hs : e.source inter s = e'.source inter s) (Heq : EqOn e e' (e.source 
inter s)) : EqOn e.symm e'.symm (e.target inter t)
参数：h : e.IsImage s t；hs : e.source inter s = e'.source inter s；Heq : EqOn e e' (
e.source inter s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn`：symm_eq_on_of_inter
_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t) (hs : e.source inter s =
 e'.source inter s) (heq : EqOn e e' (e.s…
· 使用定理 `OpenPartialHomeomorph.IsImage.toPartialEquiv`：toPartialEquiv (h : e.IsIm
age s t) : e.toPartialEquiv.IsImage s t
-/
theorem symm_eqOn_of_inter_eq_of_eqOn {e' : OpenPartialHomeomorph X Y} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq
/-
**OpenPartialHomeomorph.IsImage.map_nhdsWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ope
nPartialHomeomorph.IsImage`。
形式化陈述：map_nhdsWithin_eq (h : e.IsImage s t) (hx : x in e.source) : map e (𝓝[s] x
) = 𝓝[t] e x
参数：h : e.IsImage s t；hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.map_nhdsWithin_eq`：map_nhdsWithin_eq {x} (hx : x i
n e.source) (s : Set X) : map e (𝓝[s] x) = 𝓝[e '' (e.source inter s)] e x
· 使用定理 `OpenPartialHomeomorph.IsImage.image_eq`：image_eq (h : e.IsImage s t) : e
 '' (e.source inter s) = e.target inter t
· 使用定理 `OpenPartialHomeomorph.nhdsWithin_target_inter`：nhdsWithin_target_inter {
x} (hx : x in e.target) (s : Set Y) : 𝓝[e.target inter s] x = 𝓝[s] x
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
-/
theorem map_nhdsWithin_eq (h : e.IsImage s t) (hx : x ∈ e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhdsWithin_eq hx, h.image_eq, e.nhdsWithin_target_inter (e.map_source hx)]
/-
**OpenPartialHomeomorph.IsImage.closure** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph.IsImage`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y}, e.IsI
mage s t → e.IsImage (closure s) (closure t)
参数：closure s；closure t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.IsImage.map_nhdsWithin_eq`：map_nhdsWithin_eq (h : 
e.IsImage s t) (hx : x in e.source) : map e (𝓝[s] x) = 𝓝[t] e x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem closure (h : e.IsImage s t) : e.IsImage (closure s) (closure t) := fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhdsWithin_eq hx, map_neBot_iff]
/-
**OpenPartialHomeomorph.IsImage.interior** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph.IsImage`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y}, e.IsI
mage s t → e.IsImage (interior s) (interior t)
参数：interior s；interior t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `OpenPartialHomeomorph.IsImage.compl`：∀ {X : Type u_1} {Y : Type u_3} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeomo
rph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.closure`：∀ {X : Type u_1} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeo
morph X Y} {s : Set X} {t :…
-/
protected theorem interior (h : e.IsImage s t) : e.IsImage (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl
/-
**OpenPartialHomeomorph.IsImage.frontier** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph.IsImage`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e : OpenPartialHomeomorph X Y} {s : Set X} {t : Set Y}, e.IsI
mage s t → e.IsImage (frontier s) (frontier t)
参数：frontier s；frontier t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.diff`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeomor
ph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.closure`：∀ {X : Type u_1} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeo
morph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.interior`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHome
omorph X Y} {s : Set X} {t :…
-/
protected theorem frontier (h : e.IsImage s t) : e.IsImage (frontier s) (frontier t) :=
  h.closure.diff h.interior
/-
**OpenPartialHomeomorph.IsImage.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartia
lHomeomorph.IsImage`。
形式化陈述：isOpen_iff (h : e.IsImage s t) : IsOpen (e.source inter s) ↔ IsOpen (e.tar
get inter t)
参数：h : e.IsImage s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage`：isOpen_inter_preimage {s : 
Set Y} (hs : IsOpen s) : IsOpen (e.source inter e ⁻¹' s)
· 使用定理 `OpenPartialHomeomorph.IsImage.symm_preimage_eq'`：∀ {X : Type u_1} {Y : T
ype u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPa
rtialHomeomorph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.preimage_eq'`：∀ {X : Type u_1} {Y : Type u
_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartial
Homeomorph X Y} {s : Set X} {t :…
-/
theorem isOpen_iff (h : e.IsImage s t) : IsOpen (e.source ∩ s) ↔ IsOpen (e.target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.isOpen_inter_preimage hs, fun hs =>
    h.preimage_eq' ▸ e.isOpen_inter_preimage hs⟩

/-- Restrict an `OpenPartialHomeomorph` to a pair of corresponding open sets. -/
@[simps! -fullyApplied apply symm_apply toPartialHomeomorph]
/-
**OpenPartialHomeomorph.IsImage.restr** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHome
omorph.IsImage`。
形式化陈述：restr (h : e.IsImage s t) (hs : IsOpen (e.source inter s)) : OpenPartialHo
meomorph X Y where toPartialEquiv
参数：h : e.IsImage s t；hs : IsOpen (e.source inter s)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.toPartialEquiv`：toPartialEquiv (h : e.IsIm
age s t) : e.toPartialEquiv.IsImage s t

--- 原说明 ---
Restrict an `OpenPartialHomeomorph` to a pair of corresponding open sets.
-/
def restr (h : e.IsImage s t) (hs : IsOpen (e.source ∩ s)) : OpenPartialHomeomorph X Y where
  toPartialEquiv := h.toPartialEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuousOn_toFun := e.continuousOn.mono inter_subset_left
  continuousOn_invFun := e.symm.continuousOn.mono inter_subset_left

end IsImage

/-
**OpenPartialHomeomorph.isImage_source_target** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：isImage_source_target : e.IsImage e.source e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.isImage_source_target`：isImage_source_target : e.IsImage e.
source e.target
-/
theorem isImage_source_target : e.IsImage e.source e.target :=
  e.toPartialEquiv.isImage_source_target
/-
**OpenPartialHomeomorph.isImage_source_target_of_disjoint** 是 Mathlib 中的一个定理，位于命
名空间 `OpenPartialHomeomorph`。
形式化陈述：isImage_source_target_of_disjoint (e' : OpenPartialHomeomorph X Y) (hs : D
isjoint e.source e'.source) (ht : Disjoint e.target e'.target) : e.IsImage e'.so
urce e'.target
参数：e' : OpenPartialHomeomorph X Y；hs : Disjoint e.source e'.source；ht : Disjoint
 e.target e'.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.isImage_source_target_of_disjoint`：isImage_source_target_of
_disjoint (e' : PartialEquiv α β) (hs : Disjoint e.source e'.source) (ht : Disjo
int e.target e'.target) : e.IsImage …
-/
theorem isImage_source_target_of_disjoint (e' : OpenPartialHomeomorph X Y)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht

/-- Preimage of interior or interior of preimage coincide for open partial homeomorphisms,
when restricted to the source. -/
/-
**OpenPartialHomeomorph.preimage_interior** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartial
Homeomorph`。
形式化陈述：preimage_interior (s : Set Y) : e.source inter e ⁻¹' interior s = e.source
 inter interior (e ⁻¹' s)
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.preimage_eq`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialH
omeomorph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.interior`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHome
omorph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.of_preimage_eq`：∀ {X : Type u_1} {Y : Type
 u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenParti
alHomeomorph X Y} {s : Set X} {t :…

--- 原说明 ---
Preimage of interior or interior of preimage coincide for open partial homeomorp
hisms,
when restricted to the source.
-/
theorem preimage_interior (s : Set Y) :
    e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).interior.preimage_eq
/-
**OpenPartialHomeomorph.preimage_closure** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：preimage_closure (s : Set Y) : e.source inter e ⁻¹' closure s = e.source i
nter closure (e ⁻¹' s)
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.preimage_eq`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialH
omeomorph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.closure`：∀ {X : Type u_1} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHomeo
morph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.of_preimage_eq`：∀ {X : Type u_1} {Y : Type
 u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenParti
alHomeomorph X Y} {s : Set X} {t :…
-/
theorem preimage_closure (s : Set Y) : e.source ∩ e ⁻¹' closure s = e.source ∩ closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq
/-
**OpenPartialHomeomorph.preimage_frontier** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartial
Homeomorph`。
形式化陈述：preimage_frontier (s : Set Y) : e.source inter e ⁻¹' frontier s = e.source
 inter frontier (e ⁻¹' s)
参数：s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.IsImage.preimage_eq`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialH
omeomorph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.frontier`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHome
omorph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.of_preimage_eq`：∀ {X : Type u_1} {Y : Type
 u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenParti
alHomeomorph X Y} {s : Set X} {t :…
-/
theorem preimage_frontier (s : Set Y) :
    e.source ∩ e ⁻¹' frontier s = e.source ∩ frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).frontier.preimage_eq

end IsImage


section restrOpen
/-!
## Restriction
-/

/-- Restricting an open partial homeomorphism `e` to `e.source ∩ s` when `s` is open.
This is sometimes hard to use because of the openness assumption, but it has the advantage that
when it can be used then its `PartialEquiv` is defeq to `PartialEquiv.restr`. -/
/-
**OpenPartialHomeomorph.restrOpen** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomor
ph`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} →     [inst : TopologicalSpace X] →     
  [inst_1 : TopologicalSpace Y] → OpenPartialHomeomorph X Y → (s : Set X) → IsOp
en s → OpenPartialHomeomorph X Y
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting an open partial homeomorphism `e` to `e.source ∩ s` when `s` is open
.
This is sometimes hard to use because of the openness assumption, but it has the
 advantage that
when it can be used then its `PartialEquiv` is defeq to `PartialEquiv.restr`.
-/
protected def restrOpen (s : Set X) (hs : IsOpen s) : OpenPartialHomeomorph X Y :=
  (@IsImage.of_symm_preimage_eq X Y _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.restrOpen_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：restrOpen_toPartialEquiv (s : Set X) (hs : IsOpen s) : (e.restrOpen s hs).
toPartialEquiv = e.toPartialEquiv.restr s
参数：s : Set X；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrOpen_toPartialEquiv (s : Set X) (hs : IsOpen s) :
    (e.restrOpen s hs).toPartialEquiv = e.toPartialEquiv.restr s :=
  rfl

-- Already simp via `PartialEquiv`
/-
**OpenPartialHomeomorph.restrOpen_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：restrOpen_source (s : Set X) (hs : IsOpen s) : (e.restrOpen s hs).source =
 e.source inter s
参数：s : Set X；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrOpen_source (s : Set X) (hs : IsOpen s) : (e.restrOpen s hs).source = e.source ∩ s :=
  rfl
/-
**OpenPartialHomeomorph.coe_restrOpen** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   (e : OpenPartialHomeomorph X Y) {s : Set X} (hs : IsOpen s), ↑
(e.restrOpen s hs) = ↑e
参数：e : OpenPartialHomeomorph X Y；hs : IsOpen s；e.restrOpen s hs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_restrOpen {s : Set X} (hs : IsOpen s) : ⇑(e.restrOpen s hs) = e := rfl

@[simp]
/-
**OpenPartialHomeomorph.coe_restrOpen_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartia
lHomeomorph`。
形式化陈述：coe_restrOpen_symm {s : Set X} (hs : IsOpen s) : ⇑(e.restrOpen s hs).symm 
= e.symm
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrOpen_symm {s : Set X} (hs : IsOpen s) : ⇑(e.restrOpen s hs).symm = e.symm := rfl

/-- Restricting an open partial homeomorphism `e` to `e.source ∩ interior s`. We use the interior to
make sure that the restriction is well defined whatever the set s, since open partial homeomorphisms
are by definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of partial equivalences. -/
@[simps! (attr := mfld_simps) -fullyApplied apply symm_apply,
  simps! (attr := grind =) -isSimp source target]
/-
**OpenPartialHomeomorph.restr** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} →     [inst : TopologicalSpace X] →     
  [inst_1 : TopologicalSpace Y] → OpenPartialHomeomorph X Y → Set X → OpenPartia
lHomeomorph X Y
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
protected def restr (s : Set X) : OpenPartialHomeomorph X Y :=
  e.restrOpen (interior s) isOpen_interior

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.restr_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OpenPart
ialHomeomorph`。
形式化陈述：restr_toPartialEquiv (s : Set X) : (e.restr s).toPartialEquiv = e.toPartia
lEquiv.restr (interior s)
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restr_toPartialEquiv (s : Set X) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr (interior s) :=
  rfl
/-
**OpenPartialHomeomorph.restr_source'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：restr_source' (s : Set X) (hs : IsOpen s) : (e.restr s).source = e.source 
inter s
参数：s : Set X；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restr_source' (s : Set X) (hs : IsOpen s) : (e.restr s).source = e.source ∩ s := by
  grind
/-
**OpenPartialHomeomorph.restr_toPartialEquiv'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：restr_toPartialEquiv' (s : Set X) (hs : IsOpen s) : (e.restr s).toPartialE
quiv = e.toPartialEquiv.restr s
参数：s : Set X；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.restr_toPartialEquiv`：restr_toPartialEquiv (s : Se
t X) : (e.restr s).toPartialEquiv = e.toPartialEquiv.restr (interior s)
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem restr_toPartialEquiv' (s : Set X) (hs : IsOpen s) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr s := by
  rw [e.restr_toPartialEquiv, hs.interior_eq]
/-
**OpenPartialHomeomorph.restr_eq_of_source_subset** 是 Mathlib 中的一个定理，位于命名空间 `Ope
nPartialHomeomorph`。
形式化陈述：restr_eq_of_source_subset {e : OpenPartialHomeomorph X Y} {s : Set X} (h :
 e.source subseteq s) : e.restr s = e
参数：h : e.source subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialEquiv_injective`：toPartialEquiv_injective
 : Injective (fun f => f.toPartialEquiv : OpenPartialHomeomorph X Y -> PartialEq
uiv X Y)
· 使用定理 `PartialEquiv.restr_eq_of_source_subset`：restr_eq_of_source_subset {e : P
artialEquiv α β} {s : Set α} (h : e.source subseteq s) : e.restr s = e
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem restr_eq_of_source_subset {e : OpenPartialHomeomorph X Y} {s : Set X} (h : e.source ⊆ s) :
    e.restr s = e :=
  toPartialEquiv_injective <| PartialEquiv.restr_eq_of_source_subset <|
    interior_maximal h e.open_source

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.restr_univ** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：restr_univ {e : OpenPartialHomeomorph X Y} : e.restr univ = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.restr_eq_of_source_subset`：restr_eq_of_source_subs
et {e : OpenPartialHomeomorph X Y} {s : Set X} (h : e.source subseteq s) : e.res
tr s = e
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem restr_univ {e : OpenPartialHomeomorph X Y} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)

@[simp, grind =]
/-
**OpenPartialHomeomorph.restr_source_inter** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartia
lHomeomorph`。
形式化陈述：restr_source_inter (s : Set X) : e.restr (e.source inter s) = e.restr s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.ext`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y]   (e e' : OpenPartialHomeomorph X Y
),   (∀ (x : X)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restr_source_inter (s : Set X) : e.restr (e.source ∩ s) = e.restr s := by
  refine OpenPartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) ?_
  simp [e.open_source.interior_eq, ← inter_assoc]

end restrOpen

/-!
## ofSet

The identity on a set `s`
-/
section ofSet

variable {s : Set X} (hs : IsOpen s)

/-- The identity partial equivalence on a set `s` -/
@[simps! (attr := mfld_simps) -fullyApplied apply, simps! -isSimp source target]
/-
**OpenPartialHomeomorph.ofSet** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：ofSet (s : Set X) (hs : IsOpen s) : OpenPartialHomeomorph X X where toPart
ialEquiv
参数：s : Set X；hs : IsOpen s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity partial equivalence on a set `s`
-/
def ofSet (s : Set X) (hs : IsOpen s) : OpenPartialHomeomorph X X where
  toPartialEquiv := PartialEquiv.ofSet s
  open_source := hs
  open_target := hs
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.ofSet_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OpenPart
ialHomeomorph`。
形式化陈述：ofSet_toPartialEquiv : (ofSet s hs).toPartialEquiv = PartialEquiv.ofSet s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSet_toPartialEquiv : (ofSet s hs).toPartialEquiv = PartialEquiv.ofSet s :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.ofSet_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：ofSet_symm : (ofSet s hs).symm = ofSet s hs
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSet_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.ofSet_univ_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartia
lHomeomorph`。
形式化陈述：ofSet_univ_eq_refl : ofSet univ isOpen_univ = OpenPartialHomeomorph.refl X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.ext`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y]   (e e' : OpenPartialHomeomorph X Y
),   (∀ (x : X)…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OpenPartialHomeomorph.ofSet_apply`：∀ {X : Type u_1} [inst : TopologicalS
pace X] (s : Set X) (hs : IsOpen s), ↑(OpenPartialHomeomorph.ofSet s hs) = id
· 使用定理 `OpenPartialHomeomorph.refl_apply`：∀ (X : Type u_7) [inst : TopologicalSp
ace X], ↑(OpenPartialHomeomorph.refl X) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofSet_univ_eq_refl : ofSet univ isOpen_univ = OpenPartialHomeomorph.refl X := by
  ext <;> simp

end ofSet


/-! `EqOnSource`: equivalence on their source -/
section EqOnSource

/-- `EqOnSource e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same partial equivalence. -/
/-
**OpenPartialHomeomorph.EqOnSource** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：EqOnSource (e e' : OpenPartialHomeomorph X Y) : Prop
参数：e e' : OpenPartialHomeomorph X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EqOnSource e e'` means that `e` and `e'` have the same source, and coincide the
re. They
should really be considered the same partial equivalence.
-/
def EqOnSource (e e' : OpenPartialHomeomorph X Y) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source
/-
**OpenPartialHomeomorph.eqOnSource_iff** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph`。
形式化陈述：eqOnSource_iff (e e' : OpenPartialHomeomorph X Y) : EqOnSource e e' ↔ Part
ialEquiv.EqOnSource e.toPartialEquiv e'.toPartialEquiv
参数：e e' : OpenPartialHomeomorph X Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eqOnSource_iff (e e' : OpenPartialHomeomorph X Y) :
    EqOnSource e e' ↔ PartialEquiv.EqOnSource e.toPartialEquiv e'.toPartialEquiv :=
  Iff.rfl

/-- `EqOnSource` is an equivalence relation. -/
/-
**OpenPartialHomeomorph.eqOnSourceSetoid** 是 Mathlib 中的一个实例，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：eqOnSourceSetoid : Setoid (OpenPartialHomeomorph X Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EqOnSource` is an equivalence relation.
-/
instance eqOnSourceSetoid : Setoid (OpenPartialHomeomorph X Y) :=
  { PartialEquiv.eqOnSourceSetoid.comap
    (fun x ↦ (toPartialHomeomorph x).toPartialEquiv) with r := EqOnSource }
/-
**OpenPartialHomeomorph.eqOnSource_refl** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：eqOnSource_refl : e ≈ e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
-/
theorem eqOnSource_refl : e ≈ e := Setoid.refl _

/-- If two open partial homeomorphisms are equivalent, so are their inverses. -/
/-
**OpenPartialHomeomorph.EqOnSource.symm'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph.EqOnSource`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e e' : OpenPartialHomeomorph X Y}, e ≈ e' → e.symm ≈ e'.symm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.EqOnSource.symm'`：∀ {α : Type u_1} {β : Type u_2} {e e' : P
artialEquiv α β}, e ≈ e' → e.symm ≈ e'.symm

--- 原说明 ---
If two open partial homeomorphisms are equivalent, so are their inverses.
-/
theorem EqOnSource.symm' {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') : e.symm ≈ e'.symm :=
  PartialEquiv.EqOnSource.symm' h

/-- Two equivalent open partial homeomorphisms have the same source. -/
/-
**OpenPartialHomeomorph.EqOnSource.source_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenPart
ialHomeomorph.EqOnSource`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e e' : OpenPartialHomeomorph X Y}, e ≈ e' → e.source = e'.sou
rce
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Two equivalent open partial homeomorphisms have the same source.
-/
theorem EqOnSource.source_eq {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') :
    e.source = e'.source :=
  h.1

/-- Two equivalent open partial homeomorphisms have the same target. -/
/-
**OpenPartialHomeomorph.EqOnSource.target_eq** 是 Mathlib 中的一个定理，位于命名空间 `OpenPart
ialHomeomorph.EqOnSource`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e e' : OpenPartialHomeomorph X Y}, e ≈ e' → e.target = e'.tar
get
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `OpenPartialHomeomorph.EqOnSource.symm'`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e e' : OpenPartialH
omeomorph X Y}, e ≈ e' → e.s…

--- 原说明 ---
Two equivalent open partial homeomorphisms have the same target.
-/
theorem EqOnSource.target_eq {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') :
    e.target = e'.target :=
  h.symm'.1

/-- Two equivalent open partial homeomorphisms have coinciding `toFun` on the source -/
/-
**OpenPartialHomeomorph.EqOnSource.eqOn** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph.EqOnSource`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e e' : OpenPartialHomeomorph X Y}, e ≈ e' → Set.EqOn (↑e) (↑e
') e.source
参数：↑e；↑e'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Two equivalent open partial homeomorphisms have coinciding `toFun` on the source
-/
theorem EqOnSource.eqOn {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') : EqOn e e' e.source :=
  h.2

/-- Two equivalent open partial homeomorphisms have coinciding `invFun` on the target -/
/-
**OpenPartialHomeomorph.EqOnSource.symm_eqOn_target** 是 Mathlib 中的一个定理，位于命名空间 `O
penPartialHomeomorph.EqOnSource`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e e' : OpenPartialHomeomorph X Y}, e ≈ e' → Set.EqOn (↑e.symm
) (↑e'.symm) e.target
参数：↑e.symm；↑e'.symm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `OpenPartialHomeomorph.EqOnSource.symm'`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e e' : OpenPartialH
omeomorph X Y}, e ≈ e' → e.s…

--- 原说明 ---
Two equivalent open partial homeomorphisms have coinciding `invFun` on the targe
t
-/
theorem EqOnSource.symm_eqOn_target {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2

/-- Restriction of open partial homeomorphisms respects equivalence -/
/-
**OpenPartialHomeomorph.EqOnSource.restr** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph.EqOnSource`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e e' : OpenPartialHomeomorph X Y}, e ≈ e' → ∀ (s : Set X), e.
restr s ≈ e'.restr s
参数：s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.EqOnSource.restr`：∀ {α : Type u_1} {β : Type u_2} {e e' : P
artialEquiv α β}, e ≈ e' → ∀ (s : Set α), e.restr s ≈ e'.restr s

--- 原说明 ---
Restriction of open partial homeomorphisms respects equivalence
-/
theorem EqOnSource.restr {e e' : OpenPartialHomeomorph X Y} (he : e ≈ e') (s : Set X) :
    e.restr s ≈ e'.restr s :=
  PartialEquiv.EqOnSource.restr he _

/-- Two equivalent open partial homeomorphisms are equal when the source and target are `univ`. -/
/-
**OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph.Set.EqOn`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   {e e' : OpenPartialHomeomorph X Y}, Set.EqOn (↑e) (↑e') (e.sou
rce ∩ e'.source) → e.restr e'.source ≈ e'.restr e.source
参数：↑e；↑e'；e.source ∩ e'.source。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.restr_source'`：restr_source' (s : Set X) (hs : IsO
pen s) : (e.restr s).source = e.source inter s
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.restr_apply`：∀ {X : Type u_1} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorp
h X Y) (s : Set X), ↑(e…

--- 原说明 ---
Two equivalent open partial homeomorphisms are equal when the source and target 
are `univ`.
-/
theorem Set.EqOn.restr_eqOn_source {e e' : OpenPartialHomeomorph X Y}
    (h : EqOn e e' (e.source ∩ e'.source)) : e.restr e'.source ≈ e'.restr e.source := by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine (EqOn.trans ?_ h).trans ?_ <;> simp only [mfld_simps, eqOn_refl]
/-
**OpenPartialHomeomorph.restr_eqOnSource_of_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：restr_eqOnSource_of_eqOn {e e' : OpenPartialHomeomorph X Y} {s : Set X} (h
eq : EqOn e e' (e'.source inter interior s)) (hsub : e'.source inter interior s 
subseteq e.source) : e.restr (e'.source inter interior s) ≈ e'.restr s
参数：heq : EqOn e e' (e'.source inter interior s)；hsub : e'.source inter interior 
s subseteq e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.restr_source`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) (s : Set X), (e.…
· 使用定理 `OpenPartialHomeomorph.restr_source'`：restr_source' (s : Set X) (hs : IsO
pen s) : (e.restr s).source = e.source inter s
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `interior_interior`：interior_interior : interior (interior s) = interior 
s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem restr_eqOnSource_of_eqOn {e e' : OpenPartialHomeomorph X Y} {s : Set X}
    (heq : EqOn e e' (e'.source ∩ interior s)) (hsub : e'.source ∩ interior s ⊆ e.source) :
    e.restr (e'.source ∩ interior s) ≈ e'.restr s := by
  refine ⟨?_, fun z hz ↦ heq (by simpa [e'.open_source.interior_eq] using hz.2)⟩
  rw [e'.restr_source s, e.restr_source' _ (e'.open_source.inter isOpen_interior),
    inter_eq_right.mpr hsub]
/-
**OpenPartialHomeomorph.restr_eqOnSource_of_eqOn'** 是 Mathlib 中的一个定理，位于命名空间 `Ope
nPartialHomeomorph`。
形式化陈述：restr_eqOnSource_of_eqOn' {e e' : OpenPartialHomeomorph X Y} {s : Set X} (
hs : IsOpen s) (heq : EqOn e e' s) (hsub : e'.source inter s subseteq e.source) 
: e.restr (e'.source inter s) ≈ e'.restr s
参数：hs : IsOpen s；heq : EqOn e e' s；hsub : e'.source inter s subseteq e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.restr_eqOnSource_of_eqOn`：restr_eqOnSource_of_eqOn
 {e e' : OpenPartialHomeomorph X Y} {s : Set X} (heq : EqOn e e' (e'.source inte
r interior s)) (hsub : e'.source int…
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem restr_eqOnSource_of_eqOn' {e e' : OpenPartialHomeomorph X Y} {s : Set X} (hs : IsOpen s)
    (heq : EqOn e e' s) (hsub : e'.source ∩ s ⊆ e.source) :
    e.restr (e'.source ∩ s) ≈ e'.restr s :=
  (hs.interior_eq ▸ restr_eqOnSource_of_eqOn) (heq.mono Set.inter_subset_right) hsub
/-
**OpenPartialHomeomorph.eq_of_eqOnSource_univ** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：eq_of_eqOnSource_univ {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') (s :
 e.source = univ) (t : e.target = univ) : e = e'
参数：h : e ≈ e'；s : e.source = univ；t : e.target = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialEquiv_injective`：toPartialEquiv_injective
 : Injective (fun f => f.toPartialEquiv : OpenPartialHomeomorph X Y -> PartialEq
uiv X Y)
· 使用定理 `PartialEquiv.eq_of_eqOnSource_univ`：eq_of_eqOnSource_univ (e e' : Partia
lEquiv α β) (h : e ≈ e') (s : e.source = univ) (t : e.target = univ) : e = e'
-/
theorem eq_of_eqOnSource_univ {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  toPartialEquiv_injective <| PartialEquiv.eq_of_eqOnSource_univ _ _ h s t

variable {s : Set X}
/-
**OpenPartialHomeomorph.restr_eqOnSource_restr** 是 Mathlib 中的一个引理，位于命名空间 `OpenPa
rtialHomeomorph`。
形式化陈述：restr_eqOnSource_restr {s' : Set X} (hss' : e.source inter interior s = e.
source inter interior s') : e.restr s ≈ e.restr s'
参数：hss' : e.source inter interior s = e.source inter interior s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.restr_apply`：∀ {X : Type u_1} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorp
h X Y) (s : Set X), ↑(e…
-/
lemma restr_eqOnSource_restr {s' : Set X}
    (hss' : e.source ∩ interior s = e.source ∩ interior s') :
    e.restr s ≈ e.restr s' := by
  constructor
  · simpa [e.restr_source]
  · simp [Set.eqOn_refl]
/-
**OpenPartialHomeomorph.restr_inter_source** 是 Mathlib 中的一个引理，位于命名空间 `OpenPartia
lHomeomorph`。
形式化陈述：restr_inter_source : e.restr (e.source inter s) ≈ e.restr s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OpenPartialHomeomorph.restr_eqOnSource_restr`：restr_eqOnSource_restr {s'
 : Set X} (hss' : e.source inter interior s = e.source inter interior s') : e.re
str s ≈ e.restr s'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `interior_eq_iff_isOpen`：interior_eq_iff_isOpen : interior s = s ↔ IsOpen
 s
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
lemma restr_inter_source : e.restr (e.source ∩ s) ≈ e.restr s :=
  e.restr_eqOnSource_restr (by simp [interior_eq_iff_isOpen.mpr e.open_source])

end EqOnSource

end OpenPartialHomeomorph

namespace Homeomorph

variable (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)

/- Register as simp lemmas that the fields of an open partial homeomorphism built from a
homeomorphism correspond to the fields of the original homeomorphism. -/

@[simp, mfld_simps]
/-
**Homeomorph.refl_toOpenPartialHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`
。
形式化陈述：refl_toOpenPartialHomeomorph : (Homeomorph.refl X).toOpenPartialHomeomorph
 = OpenPartialHomeomorph.refl X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Register as simp lemmas that the fields of an open partial homeomorphism built f
rom a
homeomorphism correspond to the fields of the original homeomorphism.
-/
theorem refl_toOpenPartialHomeomorph :
    (Homeomorph.refl X).toOpenPartialHomeomorph = OpenPartialHomeomorph.refl X :=
  rfl

@[simp, mfld_simps]
/-
**Homeomorph.symm_toOpenPartialHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`
。
形式化陈述：symm_toOpenPartialHomeomorph : e.symm.toOpenPartialHomeomorph = e.toOpenPa
rtialHomeomorph.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toOpenPartialHomeomorph :
    e.symm.toOpenPartialHomeomorph = e.toOpenPartialHomeomorph.symm :=
  rfl

end Homeomorph

