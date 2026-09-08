/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
/-!
# Partial homeomorphisms: composition

## Main definitions

* `OpenPartialHomeomorph.trans`: the composition of two open partial homeomorphisms
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-!
## Composition

`trans`: composition of two open partial homeomorphisms
-/
section trans

variable (e' : OpenPartialHomeomorph Y Z)

/-- Composition of two open partial homeomorphisms when the target of the first and the source of
the second coincide. -/
@[simps! apply symm_apply toPartialHomeomorph, simps! -isSimp source target]
/-
**OpenPartialHomeomorph.trans'** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`
。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} →     {Z : Type u_5} →       [inst : Top
ologicalSpace X] →         [inst_1 : TopologicalSpace Y] →           [inst_2 : T
opologicalSpace Z] →             (e : OpenPartialHomeomorph X Y) →              
 (e' : OpenPartialHomeomorph Y Z) → e.target = e'.source → OpenPartialHomeomorph
 X Z
参数：e : OpenPartialHomeomorph X Y；e' : OpenPartialHomeomorph Y Z。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
Composition of two open partial homeomorphisms when the target of the first and 
the source of
the second coincide.
-/
protected def trans' (h : e.target = e'.source) : OpenPartialHomeomorph X Z where
  toPartialEquiv := PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  open_source := e.open_source
  open_target := e'.open_target
  continuousOn_toFun := e'.continuousOn.comp e.continuousOn <| h ▸ e.mapsTo
  continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm <| h.symm ▸ e'.mapsTo_symm

/-- Composing two open partial homeomorphisms, by restricting to the maximal domain where their
composition is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ₕ f` for this. -/
@[trans]
/-
**OpenPartialHomeomorph.trans** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：{X : Type u_1} →   {Y : Type u_3} →     {Z : Type u_5} →       [inst : Top
ologicalSpace X] →         [inst_1 : TopologicalSpace Y] →           [inst_2 : T
opologicalSpace Z] →             OpenPartialHomeomorph X Y → OpenPartialHomeomor
ph Y Z → OpenPartialHomeomorph X Z
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
Composing two open partial homeomorphisms, by restricting to the maximal domain 
where their
composition is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ₕ f` for this.
-/
protected def trans : OpenPartialHomeomorph X Z :=
  OpenPartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.trans_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OpenPart
ialHomeomorph`。
形式化陈述：trans_toPartialEquiv : (e.trans e').toPartialEquiv = e.toPartialEquiv.tran
s e'.toPartialEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomor
ph`。
形式化陈述：coe_trans : (e.trans e' : X -> Z) = e' ∘ e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans : (e.trans e' : X → Z) = e' ∘ e :=
  rfl

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.coe_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph`。
形式化陈述：coe_trans_symm : ((e.trans e').symm : Z -> X) = e.symm ∘ e'.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans_symm : ((e.trans e').symm : Z → X) = e.symm ∘ e'.symm :=
  rfl
/-
**OpenPartialHomeomorph.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：trans_apply {x : X} : (e.trans e') x = e' (e x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply {x : X} : (e.trans e') x = e' (e x) :=
  rfl
/-
**OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 
`OpenPartialHomeomorph`。
形式化陈述：trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl

/-- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
/-
**OpenPartialHomeomorph.trans_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：trans_source : (e.trans e').source = e.source inter e ⁻¹' e'.source
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.trans_source`：trans_source : (e.trans e').source = e.source
 inter e ⁻¹' e'.source

--- 原说明 ---
This could be considered as a simp lemma, but there are many situations where it
 makes something
simple into something more complicated.
-/
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  PartialEquiv.trans_source e.toPartialEquiv e'.toPartialEquiv
/-
**OpenPartialHomeomorph.trans_source'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：trans_source' : (e.trans e').source = e.source inter e ⁻¹' (e.target inter
 e'.source)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.trans_source'`：trans_source' : (e.trans e').source = e.sour
ce inter e ⁻¹' (e.target inter e'.source)
-/
theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source' e.toPartialEquiv e'.toPartialEquiv
/-
**OpenPartialHomeomorph.trans_source''** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph`。
形式化陈述：trans_source'' : (e.trans e').source = e.symm '' (e.target inter e'.source
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.trans_source''`：trans_source'' : (e.trans e').source = e.sy
mm '' (e.target inter e'.source)
-/
theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source'' e.toPartialEquiv e'.toPartialEquiv
/-
**OpenPartialHomeomorph.image_trans_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartia
lHomeomorph`。
形式化陈述：image_trans_source : e '' (e.trans e').source = e.target inter e'.source
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_trans_source`：image_trans_source : e '' (e.trans e').
source = e.target inter e'.source
-/
theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  PartialEquiv.image_trans_source e.toPartialEquiv e'.toPartialEquiv
/-
**OpenPartialHomeomorph.trans_target** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：trans_target : (e.trans e').target = e'.target inter e'.symm ⁻¹' e.target
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
/-
**OpenPartialHomeomorph.trans_target'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：trans_target' : (e.trans e').target = e'.target inter e'.symm ⁻¹' (e'.sour
ce inter e.target)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.trans_source'`：trans_source' : (e.trans e').source
 = e.source inter e ⁻¹' (e.target inter e'.source)
-/
theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
/-
**OpenPartialHomeomorph.trans_target''** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph`。
形式化陈述：trans_target'' : (e.trans e').target = e' '' (e'.source inter e.target)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.trans_source''`：trans_source'' : (e.trans e').sour
ce = e.symm '' (e.target inter e'.source)
-/
theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
/-
**OpenPartialHomeomorph.inv_image_trans_target** 是 Mathlib 中的一个定理，位于命名空间 `OpenPa
rtialHomeomorph`。
形式化陈述：inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source inter 
e.target
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.image_trans_source`：image_trans_source : e '' (e.t
rans e').source = e.target inter e'.source
-/
theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
/-
**OpenPartialHomeomorph.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：trans_assoc (e'' : OpenPartialHomeomorph Z Z') : (e.trans e').trans e'' = 
e.trans (e'.trans e'')
参数：e'' : OpenPartialHomeomorph Z Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialEquiv_injective`：toPartialEquiv_injective
 : Injective (fun f => f.toPartialEquiv : OpenPartialHomeomorph X Y -> PartialEq
uiv X Y)
· 使用定理 `PartialEquiv.trans_assoc`：trans_assoc (e'' : PartialEquiv γ δ) : (e.tran
s e').trans e'' = e.trans (e'.trans e'')
-/
theorem trans_assoc (e'' : OpenPartialHomeomorph Z Z') :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  toPartialEquiv_injective <| e.1.trans_assoc _ _

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：trans_refl : e.trans (OpenPartialHomeomorph.refl Y) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialHomeomorph_injective`：∀ {X : Type u_1} {Y
 : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Functi
on.Injective OpenPartialHomeomorph.toPart…
· 使用定理 `PartialHomeomorph.toPartialEquiv_injective`：∀ {X : Type u_1} {Y : Type u
_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Function.Inject
ive PartialHomeomorph.toPartialE…
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
-/
theorem trans_refl : e.trans (OpenPartialHomeomorph.refl Y) = e :=
  toPartialHomeomorph_injective (PartialHomeomorph.toPartialEquiv_injective e.1.trans_refl)

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：refl_trans : (OpenPartialHomeomorph.refl X).trans e = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialHomeomorph_injective`：∀ {X : Type u_1} {Y
 : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Functi
on.Injective OpenPartialHomeomorph.toPart…
· 使用定理 `PartialHomeomorph.toPartialEquiv_injective`：∀ {X : Type u_1} {Y : Type u
_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Function.Inject
ive PartialHomeomorph.toPartialE…
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
-/
theorem refl_trans : (OpenPartialHomeomorph.refl X).trans e = e :=
  toPartialHomeomorph_injective (PartialHomeomorph.toPartialEquiv_injective e.1.refl_trans)
/-
**OpenPartialHomeomorph.trans_ofSet** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：trans_ofSet {s : Set Y} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (
e ⁻¹' s)
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.ext`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y]   (e e' : OpenPartialHomeomorph X Y
),   (∀ (x : X)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.trans_source`：trans_source : (e.trans e').source =
 e.source inter e ⁻¹' e'.source
· 使用定理 `OpenPartialHomeomorph.restr_source`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) (s : Set X), (e.…
· 使用定理 `OpenPartialHomeomorph.ofSet_source`：∀ {X : Type u_1} [inst : Topological
Space X] (s : Set X) (hs : IsOpen s), (OpenPartialHomeomorph.ofSet s hs).source 
= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.preimage_interior`：preimage_interior (s : Set Y) :
 e.source inter e ⁻¹' interior s = e.source inter interior (e ⁻¹' s)
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem trans_ofSet {s : Set Y} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <| by
    rw [trans_source, restr_source, ofSet_source, ← preimage_interior, hs.interior_eq]
/-
**OpenPartialHomeomorph.trans_of_set'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：trans_of_set' {s : Set Y} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr
 (e.source inter e ⁻¹' s)
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.trans_ofSet`：trans_ofSet {s : Set Y} (hs : IsOpen 
s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s)
· 使用定理 `OpenPartialHomeomorph.restr_source_inter`：restr_source_inter (s : Set X)
 : e.restr (e.source inter s) = e.restr s
-/
theorem trans_of_set' {s : Set Y} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source ∩ e ⁻¹' s) := by rw [trans_ofSet, restr_source_inter]
/-
**OpenPartialHomeomorph.ofSet_trans** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：ofSet_trans {s : Set X} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.ext`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y]   (e e' : OpenPartialHomeomorph X Y
),   (∀ (x : X)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofSet_trans {s : Set X} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <|
    by simp [hs.interior_eq, inter_comm]
/-
**OpenPartialHomeomorph.ofSet_trans'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：ofSet_trans' {s : Set X} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr 
(e.source inter s)
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.ofSet_trans`：ofSet_trans {s : Set X} (hs : IsOpen 
s) : (ofSet s hs).trans e = e.restr s
· 使用定理 `OpenPartialHomeomorph.restr_source_inter`：restr_source_inter (s : Set X)
 : e.restr (e.source inter s) = e.restr s
-/
theorem ofSet_trans' {s : Set X} (hs : IsOpen s) :
    (ofSet s hs).trans e = e.restr (e.source ∩ s) := by
  rw [ofSet_trans, restr_source_inter]

@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.ofSet_trans_ofSet** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartial
Homeomorph`。
形式化陈述：ofSet_trans_ofSet {s : Set X} (hs : IsOpen s) {s' : Set X} (hs' : IsOpen s
') : (ofSet s hs).trans (ofSet s' hs') = ofSet (s inter s') (IsOpen.inter hs hs'
)
参数：hs : IsOpen s；hs' : IsOpen s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.trans_ofSet`：trans_ofSet {s : Set Y} (hs : IsOpen 
s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s)
· 使用定理 `OpenPartialHomeomorph.ext`：∀ {X : Type u_1} {Y : Type u_3} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y]   (e e' : OpenPartialHomeomorph X Y
),   (∀ (x : X)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.ofSet_apply`：∀ {X : Type u_1} [inst : TopologicalS
pace X] (s : Set X) (hs : IsOpen s), ↑(OpenPartialHomeomorph.ofSet s hs) = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OpenPartialHomeomorph.restr_apply`：∀ {X : Type u_1} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorp
h X Y) (s : Set X), ↑(e…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OpenPartialHomeomorph.restr_symm_apply`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHome
omorph X Y) (s : Set X), ↑(e…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofSet_trans_ofSet {s : Set X} (hs : IsOpen s) {s' : Set X} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') := by
  rw [(ofSet s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]
/-
**OpenPartialHomeomorph.restr_trans** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：restr_trans (s : Set X) : (e.restr s).trans e' = (e.trans e').restr s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialEquiv_injective`：toPartialEquiv_injective
 : Injective (fun f => f.toPartialEquiv : OpenPartialHomeomorph X Y -> PartialEq
uiv X Y)
· 使用定理 `PartialEquiv.restr_trans`：restr_trans (s : Set α) : (e.restr s).trans e'
 = (e.trans e').restr s
-/
theorem restr_trans (s : Set X) : (e.restr s).trans e' = (e.trans e').restr s :=
  toPartialEquiv_injective <|
    PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv (interior s)

end trans

/-- Composition of open partial homeomorphisms respects equivalence. -/
/-
**OpenPartialHomeomorph.EqOnSource.trans'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartial
Homeomorph.EqOnSource`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_3} {Z : Type u_5} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {e e' : OpenParti
alHomeomorph X Y} {f f' : OpenPartialHomeomorph Y Z},   e ≈ e' → f ≈ f' → e.tran
s f ≈ e'.trans f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.EqOnSource.trans'`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {e e' : PartialEquiv α β} {f f' : PartialEquiv β γ},   e ≈ e' → f ≈ f' → 
e.trans f ≈ e'.trans…

--- 原说明 ---
Composition of open partial homeomorphisms respects equivalence.
-/
theorem EqOnSource.trans' {e e' : OpenPartialHomeomorph X Y} {f f' : OpenPartialHomeomorph Y Z}
    (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  PartialEquiv.EqOnSource.trans' he hf

/-- Composition of an open partial homeomorphism and its inverse is equivalent to the restriction of
the identity to the source -/
/-
**OpenPartialHomeomorph.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：self_trans_symm : e.trans e.symm ≈ OpenPartialHomeomorph.ofSet e.source e.
open_source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.self_trans_symm`：self_trans_symm : e.trans e.symm ≈ ofSet e
.source

--- 原说明 ---
Composition of an open partial homeomorphism and its inverse is equivalent to th
e restriction of
the identity to the source
-/
theorem self_trans_symm : e.trans e.symm ≈ OpenPartialHomeomorph.ofSet e.source e.open_source :=
  PartialEquiv.self_trans_symm _
/-
**OpenPartialHomeomorph.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：symm_trans_self : e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.
open_target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.self_trans_symm`：self_trans_symm : e.trans e.symm 
≈ OpenPartialHomeomorph.ofSet e.source e.open_source
-/
theorem symm_trans_self : e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.open_target :=
  e.symm.self_trans_symm

variable {s : Set X}
/-
**OpenPartialHomeomorph.restr_symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：restr_symm_trans {e' : OpenPartialHomeomorph X Y} (hs : IsOpen s) (hs' : I
sOpen (e '' s)) (hs'' : s subseteq e.source) : (e.restr s).symm.trans e' ≈ (e.sy
mm.trans e').restr (e '' s)
参数：hs : IsOpen s；hs' : IsOpen (e '' s)；hs'' : s subseteq e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `interior_eq_iff_isOpen`：interior_eq_iff_isOpen : interior s = s ↔ IsOpen
 s
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.image_source_inter_eq'`：image_source_inter_eq' (s 
: Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `OpenPartialHomeomorph.image_source_eq_target`：image_source_eq_target : e
 '' e.source = e.target
· 使用定理 `Set.image_inter_on`：image_inter_on {f : α -> β} {s t : Set α} (h : foral
l x in t, forall y in s, f x = f y -> x = y) : f '' (s inter t) = f '' s inter f
 '' t
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.restr_symm_apply`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHome
omorph X Y) (s : Set X), ↑(e…
· 使用定理 `OpenPartialHomeomorph.restr_apply`：∀ {X : Type u_1} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorp
h X Y) (s : Set X), ↑(e…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restr_symm_trans {e' : OpenPartialHomeomorph X Y}
    (hs : IsOpen s) (hs' : IsOpen (e '' s)) (hs'' : s ⊆ e.source) :
    (e.restr s).symm.trans e' ≈ (e.symm.trans e').restr (e '' s) := by
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, PartialEquiv.restr_target,
      coe_toPartialEquiv_symm, PartialEquiv.restr_coe_symm, PartialEquiv.restr_source]
    rw [interior_eq_iff_isOpen.mpr hs', interior_eq_iff_isOpen.mpr hs]
    -- Get rid of the middle term, which is merely distracting.
    rw [inter_assoc, inter_assoc, inter_comm _ (e '' s), ← inter_assoc, ← inter_assoc]
    congr 1
    -- Now, just a bunch of rewrites: should this be a separate lemma?
    rw [← image_source_inter_eq', ← image_source_eq_target]
    refine image_inter_on ?_
    intro x hx y hy h
    rw [← left_inv e hy, ← left_inv e (hs'' hx), h]
  · simp_rw [coe_trans, restr_symm_apply, restr_apply, coe_trans]
    intro x hx
    simp
/-
**OpenPartialHomeomorph.symm_trans_restr** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：symm_trans_restr (e' : OpenPartialHomeomorph X Y) (hs : IsOpen s) : e'.sym
m.trans (e.restr s) ≈ (e'.symm.trans e).restr (e'.target inter e'.symm ⁻¹' s)
参数：e' : OpenPartialHomeomorph X Y；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.image_source_inter_eq'`：image_source_inter_eq' (s 
: Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `OpenPartialHomeomorph.isOpen_image_source_inter`：isOpen_image_source_int
er {s : Set X} (hs : IsOpen s) : IsOpen (e '' (e.source inter s))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `interior_eq_iff_isOpen`：interior_eq_iff_isOpen : interior s = s ↔ IsOpen
 s
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.restr_apply`：∀ {X : Type u_1} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorp
h X Y) (s : Set X), ↑(e…
-/
theorem symm_trans_restr (e' : OpenPartialHomeomorph X Y) (hs : IsOpen s) :
    e'.symm.trans (e.restr s) ≈ (e'.symm.trans e).restr (e'.target ∩ e'.symm ⁻¹' s) := by
  have ht : IsOpen (e'.target ∩ e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, coe_toPartialEquiv_symm,
      PartialEquiv.restr_source, preimage_inter]
    -- Shuffle the intersections, pull e'.target into the interior and use interior_inter.
    rw [interior_eq_iff_isOpen.mpr hs,
      ← inter_assoc, inter_comm e'.target, inter_assoc, inter_assoc]
    congr 1
    nth_rw 2 [← interior_eq_iff_isOpen.mpr e'.open_target]
    rw [← interior_inter, ← inter_assoc, inter_self, interior_eq_iff_isOpen.mpr ht]
  · simp [Set.eqOn_refl]

end OpenPartialHomeomorph

namespace Homeomorph

variable (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)

@[simp, mfld_simps]
/-
**Homeomorph.trans_toOpenPartialHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph
`。
形式化陈述：trans_toOpenPartialHomeomorph : (e.trans e').toOpenPartialHomeomorph = e.t
oOpenPartialHomeomorph.trans e'.toOpenPartialHomeomorph
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialHomeomorph_injective`：∀ {X : Type u_1} {Y
 : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Functi
on.Injective OpenPartialHomeomorph.toPart…
· 使用定理 `PartialHomeomorph.toPartialEquiv_injective`：∀ {X : Type u_1} {Y : Type u
_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Function.Inject
ive PartialHomeomorph.toPartialE…
· 使用定理 `Equiv.trans_toPartialEquiv`：trans_toPartialEquiv : (e.trans e').toPartia
lEquiv = e.toPartialEquiv.trans e'.toPartialEquiv
-/
theorem trans_toOpenPartialHomeomorph : (e.trans e').toOpenPartialHomeomorph =
    e.toOpenPartialHomeomorph.trans e'.toOpenPartialHomeomorph :=
  OpenPartialHomeomorph.toPartialHomeomorph_injective <|
    PartialHomeomorph.toPartialEquiv_injective <| Equiv.trans_toPartialEquiv _ _

/-- Precompose an open partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
/-
**Homeomorph.transOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：transOpenPartialHomeomorph (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z) :
 OpenPartialHomeomorph X Z where toPartialEquiv
参数：e : X ≃ₜ Y；f' : OpenPartialHomeomorph Y Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
Precompose an open partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior.
-/
def transOpenPartialHomeomorph (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z) :
    OpenPartialHomeomorph X Z where
  toPartialEquiv := e.toEquiv.transPartialEquiv f'.toPartialEquiv
  open_source := f'.open_source.preimage e.continuous
  open_target := f'.open_target
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn
/-
**Homeomorph.transOpenPartialHomeomorph_eq_trans** 是 Mathlib 中的一个定理，位于命名空间 `Home
omorph`。
形式化陈述：transOpenPartialHomeomorph_eq_trans (e : X ≃ₜ Y) (f' : OpenPartialHomeomor
ph Y Z) : e.transOpenPartialHomeomorph f' = e.toOpenPartialHomeomorph.trans f'
参数：e : X ≃ₜ Y；f' : OpenPartialHomeomorph Y Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.toPartialEquiv_injective`：toPartialEquiv_injective
 : Injective (fun f => f.toPartialEquiv : OpenPartialHomeomorph X Y -> PartialEq
uiv X Y)
· 使用定理 `Equiv.transPartialEquiv_eq_trans`：transPartialEquiv_eq_trans (e : α ≃ β)
 (f' : PartialEquiv β γ) : e.transPartialEquiv f' = e.toPartialEquiv.trans f'
-/
theorem transOpenPartialHomeomorph_eq_trans (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z) :
    e.transOpenPartialHomeomorph f' = e.toOpenPartialHomeomorph.trans f' :=
  OpenPartialHomeomorph.toPartialEquiv_injective <| Equiv.transPartialEquiv_eq_trans _ _

@[simp, mfld_simps]
/-
**Homeomorph.transOpenPartialHomeomorph_trans** 是 Mathlib 中的一个定理，位于命名空间 `Homeomo
rph`。
形式化陈述：transOpenPartialHomeomorph_trans (e : X ≃ₜ Y) (f : OpenPartialHomeomorph Y
 Z) (f' : OpenPartialHomeomorph Z Z') : (e.transOpenPartialHomeomorph f).trans f
' = e.transOpenPartialHomeomorph (f.trans f')
参数：e : X ≃ₜ Y；f : OpenPartialHomeomorph Y Z；f' : OpenPartialHomeomorph Z Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Homeomorph.transOpenPartialHomeomorph_eq_trans`：transOpenPartialHomeomor
ph_eq_trans (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z) : e.transOpenPartialHo
meomorph f' = e.toOpenPartialHomeomo…
· 使用定理 `OpenPartialHomeomorph.trans_assoc`：trans_assoc (e'' : OpenPartialHomeomo
rph Z Z') : (e.trans e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transOpenPartialHomeomorph_trans (e : X ≃ₜ Y) (f : OpenPartialHomeomorph Y Z)
    (f' : OpenPartialHomeomorph Z Z') :
    (e.transOpenPartialHomeomorph f).trans f' = e.transOpenPartialHomeomorph (f.trans f') := by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc]

@[simp, mfld_simps]
/-
**Homeomorph.trans_transOpenPartialHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Homeomo
rph`。
形式化陈述：trans_transOpenPartialHomeomorph (e : X ≃ₜ Y) (e' : Y ≃ₜ Z) (f'' : OpenPar
tialHomeomorph Z Z') : (e.trans e').transOpenPartialHomeomorph f'' = e.transOpen
PartialHomeomorph (e'.transOpenPartialHomeomorph f'')
参数：e : X ≃ₜ Y；e' : Y ≃ₜ Z；f'' : OpenPartialHomeomorph Z Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.transOpenPartialHomeomorph_eq_trans`：transOpenPartialHomeomor
ph_eq_trans (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z) : e.transOpenPartialHo
meomorph f' = e.toOpenPartialHomeomo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Homeomorph.trans_toOpenPartialHomeomorph`：trans_toOpenPartialHomeomorph 
: (e.trans e').toOpenPartialHomeomorph = e.toOpenPartialHomeomorph.trans e'.toOp
enPartialHomeomorph
· 使用定理 `OpenPartialHomeomorph.trans_assoc`：trans_assoc (e'' : OpenPartialHomeomo
rph Z Z') : (e.trans e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_transOpenPartialHomeomorph (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)
    (f'' : OpenPartialHomeomorph Z Z') : (e.trans e').transOpenPartialHomeomorph f'' =
      e.transOpenPartialHomeomorph (e'.transOpenPartialHomeomorph f'') := by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc,
    trans_toOpenPartialHomeomorph]

end Homeomorph

