/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Bundle
public import Mathlib.Data.Set.Image
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Topology.Order.Basic

/-!
# Trivializations

## Main definitions

### Basic definitions

* `Bundle.Trivialization F p` : structure extending open partial homeomorphisms, defining a local
  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `Bundle.Pretrivialization F proj` : trivialization as a partial equivalence, mainly used when the
  topology on the total space has not yet been defined.

### Operations on bundles

We provide the following operations on `Trivialization`s.

* `Bundle.Trivialization.compHomeomorph`: given a local trivialization `e` of a fiber bundle
  `p : Z → B` and a homeomorphism `h : Z' ≃ₜ Z`, returns a local trivialization of the fiber bundle
  `p ∘ h`.

## Implementation notes

Previously, in mathlib, there was a structure `topological_vector_bundle.trivialization` which
extended another structure `topological_fiber_bundle.trivialization` by a linearity hypothesis. As
of PR https://github.com/leanprover-community/mathlib3/pull/17359, we have changed this to a single
structure `Bundle.Trivialization`, together with a mixin class `Bundle.Trivialization.IsLinear`.

This permits all the *data* of a vector bundle to be held at the level of fiber bundles, so that the
same trivializations can underlie an object's structure as (say) a vector bundle over `ℂ` and as a
vector bundle over `ℝ`, as well as its structure simply as a fiber bundle.

This might be a little surprising, given the general trend of the library to ever-increased
bundling.  But in this case the typical motivation for more bundling does not apply: there is no
algebraic or order structure on the whole type of linear (say) trivializations of a bundle.
Indeed, since trivializations only have meaning on their base sets (taking junk values outside), the
type of linear trivializations is not even particularly well-behaved.
-/

@[expose] public section

open TopologicalSpace Filter Set Bundle Function
open scoped Topology

variable {B : Type*} (F : Type*) {E : B → Type*}
variable {Z : Type*} [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B}

/-- This structure contains the information left for a local trivialization (which is implemented
below as `Trivialization F proj`) if the total space has not been given a topology, but we
have a topology on both the fiber and the base space. Through the construction
`topological_fiber_prebundle F proj` it will be possible to promote a
`Pretrivialization F proj` to a `Trivialization F proj`. -/
/-
**Bundle.Pretrivialization** 是 Mathlib 中的一个归纳类型，位于命名空间 `Bundle`。
形式化陈述：{B : Type u_1} →   (F : Type u_2) → {Z : Type u_4} → [TopologicalSpace B] 
→ [TopologicalSpace F] → (Z → B) → Type (max (max u_1 u_2) u_4)
参数：F : Type u_2；Z → B；max (max u_1 u_2) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This structure contains the information left for a local trivialization (which i
s implemented
below as `Trivialization F proj`) if the total space has not been given a topolo
gy, but we
have a topology on both the fiber and the base space. Through the construction
`topological_fiber_prebundle F proj` it will be possible to promote a
`Pretrivialization F proj` to a `Trivialization F proj`.
-/
structure Bundle.Pretrivialization (proj : Z → B) extends PartialEquiv Z (B × F) where
  open_target : IsOpen target
  /-- The domain of the local trivialisation (i.e., a subset of the bundle `Z`'s base):
  outside of it, the pretrivialisation returns a junk value -/
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toFun p).1 = proj p

namespace Bundle.Pretrivialization

variable {F}
variable (e : Pretrivialization F proj) {x : Z}

/-- Coercion of a pretrivialization to a function. We don't use `e.toFun` in the `CoeFun` instance
because it is actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about
`toPartialEquiv`. While we may want to switch to this behavior later, doing it mid-port will break a
lot of proofs. -/
/-
**Bundle.Pretrivialization.toFun'** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretrivializ
ation`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] → {proj : Z → B} → Bund
le.Pretrivialization F proj → Z → B × F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of a pretrivialization to a function. We don't use `e.toFun` in the `Co
eFun` instance
because it is actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas abo
ut
`toPartialEquiv`. While we may want to switch to this behavior later, doing it m
id-port will break a
lot of proofs.
-/
@[coe] def toFun' : Z → (B × F) := e.toFun
/-
**Bundle.Pretrivialization.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle.Pretrivialization`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of a pretrivialization to a function. We don't use `e.toFun` in the `Co
eFun` instance
because it is actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas abo
ut
`toPartialEquiv`. While we may want to switch to this behavior later, doing it m
id-port will break a
lot of proofs.
-/
instance : CoeFun (Pretrivialization F proj) fun _ => Z → B × F := ⟨toFun'⟩

@[ext]
/-
**Bundle.Pretrivialization.ext'** 是 Mathlib 中的一个引理，位于命名空间 `Bundle.Pretrivializat
ion`。
形式化陈述：ext' (e e' : Pretrivialization F proj) (h₁ : e.toPartialEquiv = e'.toParti
alEquiv) (h₂ : e.baseSet = e'.baseSet) : e = e'
参数：e e' : Pretrivialization F proj；h₁ : e.toPartialEquiv = e'.toPartialEquiv；h₂ 
: e.baseSet = e'.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext' (e e' : Pretrivialization F proj) (h₁ : e.toPartialEquiv = e'.toPartialEquiv)
    (h₂ : e.baseSet = e'.baseSet) : e = e' := by
  cases e; cases e'; congr

-- TODO: tag this lemma with the `ext` attribute instead?
/-
**Bundle.Pretrivialization.ext** 是 Mathlib 中的一个引理，位于命名空间 `Bundle.Pretrivializati
on`。
形式化陈述：ext {e e' : Pretrivialization F proj} (h₁ : forall x, e x = e' x) (h₂ : fo
rall x, e.toPartialEquiv.symm x = e'.toPartialEquiv.symm x) (h₃ : e.baseSet = e'
.baseSet) : e = e'
参数：h₁ : forall x, e x = e' x；h₂ : forall x, e.toPartialEquiv.symm x = e'.toParti
alEquiv.symm x；h₃ : e.baseSet = e'.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bundle.Pretrivialization.ext'`：ext' (e e' : Pretrivialization F proj) (h
₁ : e.toPartialEquiv = e'.toPartialEquiv) (h₂ : e.baseSet = e'.baseSet) : e = e'
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
-/
lemma ext {e e' : Pretrivialization F proj} (h₁ : ∀ x, e x = e' x)
    (h₂ : ∀ x, e.toPartialEquiv.symm x = e'.toPartialEquiv.symm x) (h₃ : e.baseSet = e'.baseSet) :
    e = e' := by
  ext1 <;> [ext1; exact h₃]
  · apply h₁
  · apply h₂
  · rw [e.source_eq, e'.source_eq, h₃]

/-- If the fiber is nonempty, then the projection also is. -/
/-
**Bundle.Pretrivialization.toPartialEquiv_injective** 是 Mathlib 中的一个引理，位于命名空间 `B
undle.Pretrivialization`。
形式化陈述：toPartialEquiv_injective [Nonempty F] : Injective (toPartialEquiv : Pretri
vialization F proj -> PartialEquiv Z (B × F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bundle.Pretrivialization.ext'`：ext' (e e' : Pretrivialization F proj) (h
₁ : e.toPartialEquiv = e'.toPartialEquiv) (h₂ : e.baseSet = e'.baseSet) : e = e'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bundle.Pretrivialization.target_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `Set.fst_image_prod`：fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonem
pty) : Prod.fst '' s ×ˢ t = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If the fiber is nonempty, then the projection also is.
-/
lemma toPartialEquiv_injective [Nonempty F] :
    Injective (toPartialEquiv : Pretrivialization F proj → PartialEquiv Z (B × F)) := by
  refine fun e e' h ↦ ext' _ _ h ?_
  simpa only [fst_image_prod, univ_nonempty, target_eq]
    using congr_arg (Prod.fst '' PartialEquiv.target ·) h

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretriviali
zation`。
形式化陈述：coe_coe : ⇑e.toPartialEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe : ⇑e.toPartialEquiv = e :=
  rfl

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretriviali
zation`。
形式化陈述：coe_fst (ex : x in e.source) : (e x).1 = proj x
参数：ex : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.proj_toFun`：∀ {B : Type u_1} {F : Type u_2} {Z 
: Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z 
→ B}   (self : Bundle.Pre…
-/
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_toFun x ex
/-
**Bundle.Pretrivialization.mem_source** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretrivi
alization`。
形式化陈述：mem_source : x in e.source ↔ proj x in e.baseSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_source : x ∈ e.source ↔ proj x ∈ e.baseSet := by rw [e.source_eq, mem_preimage]
/-
**Bundle.Pretrivialization.coe_fst'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretrivial
ization`。
形式化陈述：coe_fst' (ex : proj x in e.baseSet) : (e x).1 = proj x
参数：ex : proj x in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.coe_fst`：coe_fst (ex : x in e.source) : (e x).1
 = proj x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Pretrivialization.mem_source`：mem_source : x in e.source ↔ proj x
 in e.baseSet
-/
theorem coe_fst' (ex : proj x ∈ e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)
/-
**Bundle.Pretrivialization.eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretrivializat
ion`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   (e : Bundle.Pretrivialization F 
proj), Set.EqOn (Prod.fst ∘ ↑e) proj e.source
参数：e : Bundle.Pretrivialization F proj；Prod.fst ∘ ↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.coe_fst`：coe_fst (ex : x in e.source) : (e x).1
 = proj x
-/
protected theorem eqOn : EqOn (Prod.fst ∘ e) proj e.source := fun _ hx => e.coe_fst hx

@[simp]
/-
**Bundle.Pretrivialization.mk_proj_snd** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretriv
ialization`。
形式化陈述：mk_proj_snd (ex : x in e.source) : (proj x, (e x).2) = e x
参数：ex : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Pretrivialization.coe_fst`：coe_fst (ex : x in e.source) : (e x).1
 = proj x
-/
theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl

@[simp]
/-
**Bundle.Pretrivialization.mk_proj_snd'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretri
vialization`。
形式化陈述：mk_proj_snd' (ex : proj x in e.baseSet) : (proj x, (e x).2) = e x
参数：ex : proj x in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Pretrivialization.coe_fst'`：coe_fst' (ex : proj x in e.baseSet) :
 (e x).1 = proj x
-/
theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl

/-- Composition of inverse and coercion from the subtype of the target. -/
/-
**Bundle.Pretrivialization.setSymm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretriviali
zation`。
形式化陈述：setSymm : e.target -> Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of inverse and coercion from the subtype of the target.
-/
def setSymm : e.target → Z :=
  e.target.domRestrict e.toPartialEquiv.symm
/-
**Bundle.Pretrivialization.mem_target** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretrivi
alization`。
形式化陈述：mem_target {x : B × F} : x in e.target ↔ x.1 in e.baseSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.target_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.baseSet := by
  rw [e.target_eq, prod_univ, mem_preimage]
/-
**Bundle.Pretrivialization.proj_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pre
trivialization`。
形式化陈述：proj_symm_apply {x : B × F} (hx : x in e.target) : proj (e.toPartialEquiv.
symm x) = x.1
参数：hx : x in e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Pretrivialization.coe_fst`：coe_fst (ex : x in e.source) : (e x).1
 = proj x
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `Bundle.Pretrivialization.coe_coe`：coe_coe : ⇑e.toPartialEquiv = e
-/
theorem proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.toPartialEquiv.symm x) = x.1 := by
  have := (e.coe_fst (e.map_target hx)).symm
  rwa [← e.coe_coe, e.right_inv hx] at this
/-
**Bundle.Pretrivialization.proj_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pr
etrivialization`。
形式化陈述：proj_symm_apply' {b : B} {x : F} (hx : b in e.baseSet) : proj (e.toPartial
Equiv.symm (b, x)) = b
参数：hx : b in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply`：proj_symm_apply {x : B × F} (h
x : x in e.target) : proj (e.toPartialEquiv.symm x) = x.1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Pretrivialization.mem_target`：mem_target {x : B × F} : x in e.tar
get ↔ x.1 in e.baseSet
-/
theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    proj (e.toPartialEquiv.symm (b, x)) = b :=
  e.proj_symm_apply (e.mem_target.2 hx)
/-
**Bundle.Pretrivialization.proj_surjOn_baseSet** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Pretrivialization`。
形式化陈述：proj_surjOn_baseSet [Nonempty F] : Set.SurjOn proj e.source e.baseSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Pretrivialization.mem_target`：mem_target {x : B × F} : x in e.tar
get ↔ x.1 in e.baseSet
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply'`：proj_symm_apply' {b : B} {x :
 F} (hx : b in e.baseSet) : proj (e.toPartialEquiv.symm (b, x)) = b
-/
theorem proj_surjOn_baseSet [Nonempty F] : Set.SurjOn proj e.source e.baseSet := fun b hb =>
  let ⟨y⟩ := ‹Nonempty F›
  ⟨e.toPartialEquiv.symm (b, y), e.toPartialEquiv.map_target <| e.mem_target.2 hb,
    e.proj_symm_apply' hb⟩

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pr
etrivialization`。
形式化陈述：apply_symm_apply {x : B × F} (hx : x in e.target) : e (e.toPartialEquiv.sy
mm x) = x
参数：hx : x in e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
-/
theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.toPartialEquiv.symm x) = x :=
  e.toPartialEquiv.right_inv hx

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.apply_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.P
retrivialization`。
形式化陈述：apply_symm_apply' {b : B} {x : F} (hx : b in e.baseSet) : e (e.toPartialEq
uiv.symm (b, x)) = (b, x)
参数：hx : b in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.apply_symm_apply`：apply_symm_apply {x : B × F} 
(hx : x in e.target) : e (e.toPartialEquiv.symm x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Pretrivialization.mem_target`：mem_target {x : B × F} : x in e.tar
get ↔ x.1 in e.baseSet
-/
theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    e (e.toPartialEquiv.symm (b, x)) = (b, x) :=
  e.apply_symm_apply (e.mem_target.2 hx)

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pr
etrivialization`。
形式化陈述：symm_apply_apply {x : Z} (hx : x in e.source) : e.toPartialEquiv.symm (e x
) = x
参数：hx : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
-/
theorem symm_apply_apply {x : Z} (hx : x ∈ e.source) : e.toPartialEquiv.symm (e x) = x :=
  e.toPartialEquiv.left_inv hx
/-
**Bundle.Pretrivialization.symm_apply_mk_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.
Pretrivialization`。
形式化陈述：symm_apply_mk_proj {x : Z} (ex : x in e.source) : e.toPartialEquiv.symm (p
roj x, (e x).2) = x
参数：ex : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Pretrivialization.coe_fst`：coe_fst (ex : x in e.source) : (e x).1
 = proj x
· 使用定理 `Bundle.Pretrivialization.coe_coe`：coe_coe : ⇑e.toPartialEquiv = e
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
-/
theorem symm_apply_mk_proj {x : Z} (ex : x ∈ e.source) :
    e.toPartialEquiv.symm (proj x, (e x).2) = x := by
  rw [← e.coe_fst ex, ← e.coe_coe, e.left_inv ex]

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.preimage_symm_proj_baseSet** 是 Mathlib 中的一个定理，位于命名空间 
`Bundle.Pretrivialization`。
形式化陈述：preimage_symm_proj_baseSet : e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' e.baseSet
) inter e.target = e.target
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply`：proj_symm_apply {x : B × F} (h
x : x in e.target) : proj (e.toPartialEquiv.symm x) = x.1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.Pretrivialization.mem_target`：mem_target {x : B × F} : x in e.tar
get ↔ x.1 in e.baseSet
-/
theorem preimage_symm_proj_baseSet :
    e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' e.baseSet) ∩ e.target = e.target := by
  refine inter_eq_right.mpr fun x hx => ?_
  simp only [mem_preimage, e.proj_symm_apply hx]
  exact e.mem_target.mp hx

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.preimage_symm_proj_inter** 是 Mathlib 中的一个定理，位于命名空间 `B
undle.Pretrivialization`。
形式化陈述：preimage_symm_proj_inter (s : Set B) : e.toPartialEquiv.symm ⁻¹' (proj ⁻¹'
 s) inter e.baseSet ×ˢ univ = (s inter e.baseSet) ×ˢ univ
参数：s : Set B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply'`：proj_symm_apply' {b : B} {x :
 F} (hx : b in e.baseSet) : proj (e.toPartialEquiv.symm (b, x)) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem preimage_symm_proj_inter (s : Set B) :
    e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' s) ∩ e.baseSet ×ˢ univ = (s ∩ e.baseSet) ×ˢ univ := by
  ext ⟨x, y⟩
  suffices x ∈ e.baseSet → (proj (e.toPartialEquiv.symm (x, y)) ∈ s ↔ x ∈ s) by
    simpa only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ, and_congr_left_iff]
  intro h
  rw [e.proj_symm_apply' h]
/-
**Bundle.Pretrivialization.target_inter_preimage_symm_source_eq** 是 Mathlib 中的一个
定理，位于命名空间 `Bundle.Pretrivialization`。
形式化陈述：target_inter_preimage_symm_source_eq (e f : Pretrivialization F proj) : f.
target inter f.toPartialEquiv.symm ⁻¹' e.source = (e.baseSet inter f.baseSet) ×ˢ
 univ
参数：e f : Pretrivialization F proj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Bundle.Pretrivialization.target_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `Bundle.Pretrivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `Bundle.Pretrivialization.preimage_symm_proj_inter`：preimage_symm_proj_in
ter (s : Set B) : e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' s) inter e.baseSet ×ˢ univ
 = (s inter e.baseSet) ×ˢ univ
-/
theorem target_inter_preimage_symm_source_eq (e f : Pretrivialization F proj) :
    f.target ∩ f.toPartialEquiv.symm ⁻¹' e.source = (e.baseSet ∩ f.baseSet) ×ˢ univ := by
  rw [inter_comm, f.target_eq, e.source_eq, f.preimage_symm_proj_inter]
/-
**Bundle.Pretrivialization.trans_source** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretri
vialization`。
形式化陈述：trans_source (e f : Pretrivialization F proj) : (f.toPartialEquiv.symm.tra
ns e.toPartialEquiv).source = (e.baseSet inter f.baseSet) ×ˢ univ
参数：e f : Pretrivialization F proj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.trans_source`：trans_source : (e.trans e').source = e.source
 inter e ⁻¹' e'.source
· 使用定理 `PartialEquiv.symm_source`：symm_source : e.symm.source = e.target
· 使用定理 `Bundle.Pretrivialization.target_inter_preimage_symm_source_eq`：target_in
ter_preimage_symm_source_eq (e f : Pretrivialization F proj) : f.target inter f.
toPartialEquiv.symm ⁻¹' e.source = (e.baseSet inter…
-/
theorem trans_source (e f : Pretrivialization F proj) :
    (f.toPartialEquiv.symm.trans e.toPartialEquiv).source = (e.baseSet ∩ f.baseSet) ×ˢ univ := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source, e.target_inter_preimage_symm_source_eq]
/-
**Bundle.Pretrivialization.symm_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pre
trivialization`。
形式化陈述：symm_trans_symm (e e' : Pretrivialization F proj) : (e.toPartialEquiv.symm
.trans e'.toPartialEquiv).symm = e'.toPartialEquiv.symm.trans e.toPartialEquiv
参数：e e' : Pretrivialization F proj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.trans_symm_eq_symm_trans_symm`：trans_symm_eq_symm_trans_sym
m : (e.trans e').symm = e'.symm.trans e.symm
· 使用定理 `PartialEquiv.symm_symm`：symm_symm : e.symm.symm = e
-/
theorem symm_trans_symm (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).symm
      = e'.toPartialEquiv.symm.trans e.toPartialEquiv := by
  rw [PartialEquiv.trans_symm_eq_symm_trans_symm, PartialEquiv.symm_symm]
/-
**Bundle.Pretrivialization.symm_trans_source_eq** 是 Mathlib 中的一个定理，位于命名空间 `Bundl
e.Pretrivialization`。
形式化陈述：symm_trans_source_eq (e e' : Pretrivialization F proj) : (e.toPartialEquiv
.symm.trans e'.toPartialEquiv).source = (e.baseSet inter e'.baseSet) ×ˢ univ
参数：e e' : Pretrivialization F proj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.trans_source`：trans_source : (e.trans e').source = e.source
 inter e ⁻¹' e'.source
· 使用定理 `Bundle.Pretrivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `PartialEquiv.symm_source`：symm_source : e.symm.source = e.target
· 使用定理 `Bundle.Pretrivialization.target_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Bundle.Pretrivialization.preimage_symm_proj_inter`：preimage_symm_proj_in
ter (s : Set B) : e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' s) inter e.baseSet ×ˢ univ
 = (s inter e.baseSet) ×ˢ univ
-/
theorem symm_trans_source_eq (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).source = (e.baseSet ∩ e'.baseSet) ×ˢ univ := by
  rw [PartialEquiv.trans_source, e'.source_eq, PartialEquiv.symm_source, e.target_eq, inter_comm,
    e.preimage_symm_proj_inter, inter_comm]
/-
**Bundle.Pretrivialization.symm_trans_target_eq** 是 Mathlib 中的一个定理，位于命名空间 `Bundl
e.Pretrivialization`。
形式化陈述：symm_trans_target_eq (e e' : Pretrivialization F proj) : (e.toPartialEquiv
.symm.trans e'.toPartialEquiv).target = (e.baseSet inter e'.baseSet) ×ˢ univ
参数：e e' : Pretrivialization F proj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.symm_source`：symm_source : e.symm.source = e.target
· 使用定理 `Bundle.Pretrivialization.symm_trans_symm`：symm_trans_symm (e e' : Pretri
vialization F proj) : (e.toPartialEquiv.symm.trans e'.toPartialEquiv).symm = e'.
toPartialEquiv.symm.trans e.to…
· 使用定理 `Bundle.Pretrivialization.symm_trans_source_eq`：symm_trans_source_eq (e e
' : Pretrivialization F proj) : (e.toPartialEquiv.symm.trans e'.toPartialEquiv).
source = (e.baseSet inter e'.baseSe…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem symm_trans_target_eq (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).target = (e.baseSet ∩ e'.baseSet) ×ˢ univ := by
  rw [← PartialEquiv.symm_source, symm_trans_symm, symm_trans_source_eq, inter_comm]

variable (e' : Pretrivialization F (π F E)) {b : B} {y : E b}

@[simp]
/-
**Bundle.Pretrivialization.coe_mem_source** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pret
rivialization`。
形式化陈述：coe_mem_source : ↑y in e'.source ↔ b in e'.baseSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.mem_source`：mem_source : x in e.source ↔ proj x
 in e.baseSet
-/
theorem coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.baseSet :=
  e'.mem_source

@[mfld_simps]
/-
**Bundle.Pretrivialization.coe_coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretriv
ialization`。
形式化陈述：coe_coe_fst (hb : b in e'.baseSet) : (e' y).1 = b
参数：hb : b in e'.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.coe_fst`：coe_fst (ex : x in e.source) : (e x).1
 = proj x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_coe_fst (hb : b ∈ e'.baseSet) : (e' y).1 = b := by
  simp [hb]
/-
**Bundle.Pretrivialization.mk_mem_target** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretr
ivialization`。
形式化陈述：mk_mem_target {x : B} {y : F} : (x, y) in e'.target ↔ x in e'.baseSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.mem_target`：mem_target {x : B × F} : x in e.tar
get ↔ x.1 in e.baseSet
-/
theorem mk_mem_target {x : B} {y : F} : (x, y) ∈ e'.target ↔ x ∈ e'.baseSet :=
  e'.mem_target

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.symm_coe_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretr
ivialization`。
形式化陈述：symm_coe_proj {x : B} {y : F} (e' : Pretrivialization F (π F E)) (h : x in
 e'.baseSet) : (e'.toPartialEquiv.symm (x, y)).1 = x
参数：e' : Pretrivialization F (π F E)；h : x in e'.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply'`：proj_symm_apply' {b : B} {x :
 F} (hx : b in e.baseSet) : proj (e.toPartialEquiv.symm (b, x)) = b
-/
theorem symm_coe_proj {x : B} {y : F} (e' : Pretrivialization F (π F E)) (h : x ∈ e'.baseSet) :
    (e'.toPartialEquiv.symm (x, y)).1 = x :=
  e'.proj_symm_apply' h

section Nonempty

variable [∀ x, Nonempty (E x)]

open scoped Classical in
/-- A fiberwise inverse to `e`. This is the function `F → E b` that induces a local inverse
`B × F → TotalSpace F E` of `e` on `e.baseSet`. Outside of `e.baseSet` it takes on arbitrarily
chosen junk values. -/
/-
**Bundle.Pretrivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretrivializat
ion`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [∀ (x :
 B), Nonempty (E x)] → Bundle.Pretrivialization F Bundle.TotalSpace.proj → (b : 
B) → F → E b
参数：x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fiberwise inverse to `e`. This is the function `F → E b` that induces a local 
inverse
`B × F → TotalSpace F E` of `e` on `e.baseSet`. Outside of `e.baseSet` it takes 
on arbitrarily
chosen junk values.
-/
protected noncomputable def symm (e : Pretrivialization F (π F E)) (b : B) (y : F) : E b :=
  if hb : b ∈ e.baseSet then
    cast (congr_arg E (e.proj_symm_apply' hb)) (e.toPartialEquiv.symm (b, y)).2
  else Classical.arbitrary _
/-
**Bundle.Pretrivialization.symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretrivi
alization`。
形式化陈述：symm_apply (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet)
 (y : F) : e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toPartialEqui
v.symm (b, y)).2
参数：e : Pretrivialization F (π F E)；hb : b in e.baseSet；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem symm_apply (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toPartialEquiv.symm (b, y)).2 :=
  dif_pos hb

@[deprecated "The junk values of `Pretrivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values." (since := "2026-06-23")]
/-
**Bundle.Pretrivialization.symm_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Bundl
e.Pretrivialization`。
形式化陈述：symm_apply_of_notMem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e
.baseSet) (y : F) : e.symm b y = Classical.arbitrary _
参数：e : Pretrivialization F (π F E)；hb : b ∉ e.baseSet；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_apply_of_notMem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet)
    (y : F) : e.symm b y = Classical.arbitrary _ := by
  simp [Pretrivialization.symm, hb]

@[deprecated "The junk values of `Pretrivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values." (since := "2026-06-23")]
/-
**Bundle.Pretrivialization.coe_symm_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.
Pretrivialization`。
形式化陈述：coe_symm_of_notMem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.b
aseSet) : e.symm b = fun _ => Classical.arbitrary _
参数：e : Pretrivialization F (π F E)；hb : b ∉ e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bundle.Pretrivialization.symm_apply_of_notMem`：symm_apply_of_notMem (e :
 Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) (y : F) : e.symm b y 
= Classical.arbitrary _
-/
theorem coe_symm_of_notMem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) :
    e.symm b = fun _ ↦ Classical.arbitrary _ := by
  ext; exact symm_apply_of_notMem e hb _
/-
**Bundle.Pretrivialization.mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretriviali
zation`。
形式化陈述：mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y
 : F) : TotalSpace.mk b (e.symm b y) = e.toPartialEquiv.symm (b, y)
参数：e : Pretrivialization F (π F E)；hb : b in e.baseSet；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.symm_coe_proj`：symm_coe_proj {x : B} {y : F} (e
' : Pretrivialization F (π F E)) (h : x in e'.baseSet) : (e'.toPartialEquiv.symm
 (x, y)).1 = x
· 使用定理 `Bundle.Pretrivialization.symm_apply`：symm_apply (e : Pretrivialization F
 (π F E)) {b : B} (hb : b in e.baseSet) (y : F) : e.symm b y = cast (congr_arg E
 (e.symm_coe_proj hb)) (e…
· 使用定理 `Bundle.TotalSpace.mk_cast`：∀ {B : Type u_1} {F : Type u_2} {E : B → Type
 u_3} {x x' : B} (h : x = x') (b : E x), ⟨x', cast ⋯ b⟩ = ⟨x, b⟩
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply'`：proj_symm_apply' {b : B} {x :
 F} (hx : b in e.baseSet) : proj (e.toPartialEquiv.symm (b, x)) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    TotalSpace.mk b (e.symm b y) = e.toPartialEquiv.symm (b, y) := by
  simp only [e.symm_apply hb, TotalSpace.mk_cast (e.proj_symm_apply' hb), TotalSpace.eta]

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.symm_proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pre
trivialization`。
形式化陈述：symm_proj_apply (e : Pretrivialization F (π F E)) (z : TotalSpace F E) (hz
 : z.proj in e.baseSet) : e.symm z.proj (e z).2 = z.2
参数：e : Pretrivialization F (π F E)；z : TotalSpace F E；hz : z.proj in e.baseSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.symm_coe_proj`：symm_coe_proj {x : B} {y : F} (e
' : Pretrivialization F (π F E)) (h : x in e'.baseSet) : (e'.toPartialEquiv.symm
 (x, y)).1 = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.symm_apply`：symm_apply (e : Pretrivialization F
 (π F E)) {b : B} (hb : b in e.baseSet) (y : F) : e.symm b y = cast (congr_arg E
 (e.symm_coe_proj hb)) (e…
· 使用定理 `cast_eq_iff_heq`：∀ {a a_1 : Sort u_1} {e : a = a_1} {a_2 : a} {a' : a_1}
, cast e a_2 = a' ↔ a_2 ≍ a'
· 使用定理 `Bundle.Pretrivialization.mk_proj_snd'`：mk_proj_snd' (ex : proj x in e.ba
seSet) : (proj x, (e x).2) = e x
· 使用定理 `Bundle.Pretrivialization.symm_apply_apply`：symm_apply_apply {x : Z} (hx 
: x in e.source) : e.toPartialEquiv.symm (e x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Pretrivialization.mem_source`：mem_source : x in e.source ↔ proj x
 in e.baseSet
-/
theorem symm_proj_apply (e : Pretrivialization F (π F E)) (z : TotalSpace F E)
    (hz : z.proj ∈ e.baseSet) : e.symm z.proj (e z).2 = z.2 := by
  rw [e.symm_apply hz, cast_eq_iff_heq, e.mk_proj_snd' hz, e.symm_apply_apply (e.mem_source.mpr hz)]

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.symm_apply_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Pretrivialization`。
形式化陈述：symm_apply_apply_mk (e : Pretrivialization F (π F E)) {b : B} (hb : b in e
.baseSet) (y : E b) : e.symm b (e ⟨b, y⟩).2 = y
参数：e : Pretrivialization F (π F E)；hb : b in e.baseSet；y : E b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.symm_proj_apply`：symm_proj_apply (e : Pretrivia
lization F (π F E)) (z : TotalSpace F E) (hz : z.proj in e.baseSet) : e.symm z.p
roj (e z).2 = z.2
-/
theorem symm_apply_apply_mk (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet)
    (y : E b) : e.symm b (e ⟨b, y⟩).2 = y :=
  e.symm_proj_apply ⟨b, y⟩ hb

@[simp, mfld_simps]
/-
**Bundle.Pretrivialization.apply_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Pretr
ivialization`。
形式化陈述：apply_mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseS
et) (y : F) : e ⟨b, e.symm b y⟩ = (b, y)
参数：e : Pretrivialization F (π F E)；hb : b in e.baseSet；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.mk_symm`：mk_symm (e : Pretrivialization F (π F 
E)) {b : B} (hb : b in e.baseSet) (y : F) : TotalSpace.mk b (e.symm b y) = e.toP
artialEquiv.symm (b, y…
· 使用定理 `Bundle.Pretrivialization.apply_symm_apply`：apply_symm_apply {x : B × F} 
(hx : x in e.target) : e (e.toPartialEquiv.symm x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Pretrivialization.mk_mem_target`：mk_mem_target {x : B} {y : F} : 
(x, y) in e'.target ↔ x in e'.baseSet
-/
theorem apply_mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e ⟨b, e.symm b y⟩ = (b, y) := by
  rw [e.mk_symm hb, e.apply_symm_apply (e.mk_mem_target.mpr hb)]

end Nonempty

/-- The restriction of a pretrivialization to a subset of the base. -/
@[simps toFun source target baseSet]
/-
**Bundle.Pretrivialization.restrictPreimage'** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.P
retrivialization`。
形式化陈述：restrictPreimage' (e : Pretrivialization F proj) (s : Set B) [Nonempty (s 
-> F -> proj ⁻¹' s)] : Pretrivialization F (s.restrictPreimage proj) where toFun
 z
参数：e : Pretrivialization F proj；s : Set B；s -> F -> proj ⁻¹' s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a pretrivialization to a subset of the base.
-/
noncomputable def restrictPreimage' (e : Pretrivialization F proj) (s : Set B)
    [Nonempty (s → F → proj ⁻¹' s)] : Pretrivialization F (s.restrictPreimage proj) where
  toFun z := (⟨proj z, z.2⟩, (e z).2)
  invFun x := by classical exact if h : (x.1.1, x.2) ∈ e.target then ⟨e.invFun (x.1, x.2), by
      simpa only [mem_preimage, ← e.proj_toFun _ (e.map_target' h), e.right_inv' h] using! x.1.2⟩
    else Classical.arbitrary (s → F → _) x.1 x.2
  source := Subtype.val ⁻¹' e.source
  target := (Prod.map Subtype.val id) ⁻¹' e.target
  map_source' z hz := by
    simpa only [Prod.map_apply, ← e.proj_toFun _ hz] using! e.map_source' hz
  map_target' x hx := by
    simp only [mem_preimage, (Prod.map_apply), id_eq] at hx
    rw [dif_pos hx]; exact e.map_target' hx
  left_inv' z hz := by
    dsimp only; rw [dif_pos] <;> all_goals simp_rw [← e.proj_toFun _ hz]
    exacts [Subtype.ext (e.left_inv' hz), e.map_source' hz]
  right_inv' x hx := Subtype.val_injective.prodMap injective_id <| by
    simp only [mem_preimage, (Prod.map_apply), id_eq] at hx
    simp_rw [Prod.map_apply]; rw [dif_pos hx]
    convert! ← e.right_inv' hx; exact e.proj_toFun _ (e.map_target' hx)
  open_target := e.open_target.preimage <| by fun_prop
  baseSet := Subtype.val ⁻¹' e.baseSet
  open_baseSet := e.open_baseSet.preimage continuous_subtype_val
  source_eq := Set.ext fun _ ↦ Set.ext_iff.mp e.source_eq _
  target_eq := Set.ext fun _ ↦ Set.ext_iff.mp e.target_eq _
  proj_toFun _ _ := rfl

/-- The restriction of a pretrivialization to a set with nonempty intersection with the base set. -/
@[simps! toFun source target baseSet]
/-
**Bundle.Pretrivialization.restrictPreimage** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pr
etrivialization`。
形式化陈述：restrictPreimage (e : Pretrivialization F proj) {s : Set B} (hs : (s inter
 e.baseSet).Nonempty) : Pretrivialization F (s.restrictPreimage proj)
参数：e : Pretrivialization F proj；hs : (s inter e.baseSet).Nonempty。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a pretrivialization to a set with nonempty intersection with 
the base set.
-/
noncomputable def restrictPreimage (e : Pretrivialization F proj) {s : Set B}
    (hs : (s ∩ e.baseSet).Nonempty) : Pretrivialization F (s.restrictPreimage proj) :=
  have : Nonempty (F → proj ⁻¹' s) := .intro fun f ↦ Nonempty.some <| have ⟨z, hzs, hzb⟩ := hs
    ⟨⟨e.invFun ⟨z, f⟩, Set.mem_preimage.mpr <| (e.proj_symm_apply' hzb).symm ▸ hzs⟩⟩
  e.restrictPreimage' s

/-- Extend the total space of a pretrivialization from the preimage of a set to the whole space. -/
@[simps invFun source target baseSet]
/-
**Bundle.Pretrivialization.domExtend** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretrivia
lization`。
形式化陈述：domExtend {s : Set B} (e : Pretrivialization F fun z : proj ⁻¹' s => proj 
z) [Nonempty (Z -> F)] : Pretrivialization F proj where toFun z
参数：e : Pretrivialization F fun z : proj ⁻¹' s => proj z；Z -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the total space of a pretrivialization from the preimage of a set to the 
whole space.
-/
noncomputable def domExtend {s : Set B} (e : Pretrivialization F fun z : proj ⁻¹' s ↦ proj z)
    [Nonempty (Z → F)] : Pretrivialization F proj where
  toFun z := by classical exact if h : proj z ∈ s then e ⟨z, h⟩
    else (proj z, Classical.arbitrary (Z → F) z)
  invFun x := e.invFun x
  source := Subtype.val '' e.source
  target := e.target
  map_source' _ := by
    rintro ⟨⟨z, hzp : proj z ∈ s⟩, hze, rfl⟩
    simpa [hzp, e.coe_fst hze] using e.map_source hze
  map_target' x hx := by simpa using ⟨(e.invFun x).2, e.map_target hx⟩
  left_inv' _ := by rintro ⟨⟨z, hzp : proj z ∈ s⟩, hze, rfl⟩; simp [hzp, e.symm_apply_apply hze]
  right_inv' x hx := (dif_pos (e.invFun x).2).trans (e.right_inv hx)
  open_target := e.open_target
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by ext z; simpa [e.source_eq] using
    (e.proj_symm_apply' · ▸ (e.invFun (proj z, Classical.arbitrary (Z → F) z)).2)
  target_eq := by ext; simp [e.target_eq]
  proj_toFun _ := by rintro ⟨⟨z, hzp : proj z ∈ s⟩, hze, rfl⟩; simp [hzp, e.coe_fst hze]

/-- Extend the base of a pretrivialization from a set to the whole space. -/
@[simps toFun source target baseSet]
/-
**Bundle.Pretrivialization.codExtend'** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretrivi
alization`。
形式化陈述：codExtend' {s : Set B} (hs : IsOpen s) {proj : Z -> s} (e : Pretrivializat
ion F proj) [Nonempty (B -> F -> Z)] : Pretrivialization F (Subtype.val ∘ proj) 
where toFun z
参数：hs : IsOpen s；e : Pretrivialization F proj；B -> F -> Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the base of a pretrivialization from a set to the whole space.
-/
noncomputable def codExtend' {s : Set B} (hs : IsOpen s) {proj : Z → s}
    (e : Pretrivialization F proj) [Nonempty (B → F → Z)] :
    Pretrivialization F (Subtype.val ∘ proj) where
  toFun z := ⟨(e z).1, (e z).2⟩
  invFun x := by classical exact if h : x.1 ∈ s then e.invFun (⟨x.1, h⟩, x.2)
    else Classical.arbitrary (B → F → Z) x.1 x.2
  source := e.source
  target := (Prod.map Subtype.val id) '' e.target
  map_source' z hz := by simpa using e.map_source hz
  map_target' _ := by rintro ⟨x, hx, rfl⟩; simpa using e.map_target hx
  left_inv' z hz := by simpa using e.left_inv hz
  right_inv' _ := by rintro ⟨x, hx, rfl⟩; ext <;> simp [e.apply_symm_apply hx]
  open_target := hs.isOpenMap_subtype_val.prodMap .id _ e.open_target
  baseSet := Subtype.val '' e.baseSet
  open_baseSet := hs.isOpenMap_subtype_val _ e.open_baseSet
  source_eq := by ext; simp [e.source_eq]
  target_eq := by rw [e.target_eq, prodMap_image_prod, image_id]
  proj_toFun _ h := by simp [e.coe_fst h]

/-- Extend the base of a pretrivialization from a nonempty set to the whole space. -/
@[simps! toFun source target baseSet]
/-
**Bundle.Pretrivialization.codExtend** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Pretrivia
lization`。
形式化陈述：codExtend {s : Set B} (hs : IsOpen s) (nonempty : s.Nonempty) {proj : Z ->
 s} (e : Pretrivialization F proj) : Pretrivialization F (Subtype.val ∘ proj)
参数：hs : IsOpen s；nonempty : s.Nonempty；e : Pretrivialization F proj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the base of a pretrivialization from a nonempty set to the whole space.
-/
noncomputable def codExtend {s : Set B} (hs : IsOpen s) (nonempty : s.Nonempty) {proj : Z → s}
    (e : Pretrivialization F proj) : Pretrivialization F (Subtype.val ∘ proj) :=
  have : Nonempty (F → Z) := .intro fun f ↦ e.invFun (⟨_, nonempty.some_mem⟩, f)
  e.codExtend' hs

end Pretrivialization

variable [TopologicalSpace Z] [TopologicalSpace (TotalSpace F E)]

/-- A structure extending open partial homeomorphisms, defining a local trivialization of a
projection `proj : Z → B` with fiber `F`, as an open partial homeomorphism between `Z` and `B × F`
defined between two sets of the form `proj ⁻¹' baseSet` and `baseSet × F`, acting trivially on the
first coordinate.
-/
/-
**Bundle.Trivialization** 是 Mathlib 中的一个归纳类型，位于命名空间 `Bundle`。
形式化陈述：{B : Type u_1} →   (F : Type u_2) →     {Z : Type u_4} →       [Topologica
lSpace B] → [TopologicalSpace F] → [TopologicalSpace Z] → (Z → B) → Type (max (m
ax u_1 u_2) u_4)
参数：F : Type u_2；Z → B；max (max u_1 u_2) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure extending open partial homeomorphisms, defining a local trivializati
on of a
projection `proj : Z → B` with fiber `F`, as an open partial homeomorphism betwe
en `Z` and `B × F`
defined between two sets of the form `proj ⁻¹' baseSet` and `baseSet × F`, actin
g trivially on the
first coordinate.
-/
structure Trivialization (proj : Z → B) extends OpenPartialHomeomorph Z (B × F) where
  /-- The domain of the local trivialisation (i.e., a subset of the bundle `Z`'s base):
  outside of it, the pretrivialisation returns a junk value -/
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toOpenPartialHomeomorph p).1 = proj p

namespace Trivialization

variable {F}
variable (e : Trivialization F proj) {x : Z}

@[ext]
/-
**Bundle.Trivialization.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 e' : Bundle.Trivialization F proj),   e.toOpenPartialHomeomorph = e'.toOpenPart
ialHomeomorph → e.baseSet = e'.baseSet → e = e'
参数：e e' : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext' (e e' : Trivialization F proj)
    (h₁ : e.toOpenPartialHomeomorph = e'.toOpenPartialHomeomorph) (h₂ : e.baseSet = e'.baseSet) :
    e = e' := by
  cases e; cases e'; congr

/-- Coercion of a trivialization to a function. We don't use `e.toFun` in the `CoeFun` instance
because it is actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about
`toPartialEquiv`. While we may want to switch to this behavior later, doing it mid-port will break a
lot of proofs. -/
/-
**Bundle.Trivialization.toFun'** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`
。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} → [inst_2 : TopologicalSpace Z] → Bundle.Trivialization F proj → Z → B × F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of a trivialization to a function. We don't use `e.toFun` in the `CoeFu
n` instance
because it is actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas abo
ut
`toPartialEquiv`. While we may want to switch to this behavior later, doing it m
id-port will break a
lot of proofs.
-/
@[coe] def toFun' : Z → (B × F) := e.toFun

/-- Natural identification as a `Pretrivialization`. -/
/-
**Bundle.Trivialization.toPretrivialization** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Tr
ivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] → Bundle.Trivialization F proj →
 Bundle.Pretrivialization F proj
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Bundle.Trivialization.target_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Bundle.Trivialization.proj_toFun`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : T
opologicalSpace Z] {pr…

--- 原说明 ---
Natural identification as a `Pretrivialization`.
-/
def toPretrivialization : Pretrivialization F proj :=
  { e with }
/-
**Bundle.Trivialization.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle.Trivialization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (Trivialization F proj) fun _ => Z → B × F := ⟨toFun'⟩
/-
**Bundle.Trivialization.** 是 Mathlib 中的一个实例，位于命名空间 `Bundle.Trivialization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (Trivialization F proj) (Pretrivialization F proj) :=
  ⟨toPretrivialization⟩

/-- See Note [custom simps projection] -/
/-
**Bundle.Trivialization.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializa
tion.Simps`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2 : T
opologicalSpace Z] → (proj : Z → B) → Bundle.Trivialization F proj → Z → B × F
参数：proj : Z → B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (proj : Z → B) (e : Trivialization F proj) : Z → B × F := e

/-- See Note [custom simps projection] -/
/-
**Bundle.Trivialization.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivi
alization.Simps`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2 : T
opologicalSpace Z] → (proj : Z → B) → Bundle.Trivialization F proj → B × F → Z
参数：proj : Z → B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
noncomputable def Simps.symm_apply (proj : Z → B) (e : Trivialization F proj) : B × F → Z :=
  e.toOpenPartialHomeomorph.symm

initialize_simps_projections Trivialization (toFun → apply, invFun → symm_apply)
/-
**Bundle.Trivialization.toPretrivialization_injective** 是 Mathlib 中的一个定理，位于命名空间 
`Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z], F
unction.Injective fun e => e.toPretrivialization
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.ext'`：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_
4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}   [i
nst_2 : Topologi…
· 使用定理 `OpenPartialHomeomorph.toPartialEquiv_injective`：toPartialEquiv_injective
 : Injective (fun f => f.toPartialEquiv : OpenPartialHomeomorph X Y -> PartialEq
uiv X Y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toPretrivialization_injective :
    Function.Injective fun e : Trivialization F proj => e.toPretrivialization := fun e e' h => by
  ext1
  exacts [OpenPartialHomeomorph.toPartialEquiv_injective congr(Pretrivialization.toPartialEquiv $h),
    congr(Pretrivialization.baseSet $h)]

@[simp, mfld_simps]
/-
**Bundle.Trivialization.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivialization
`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj), ↑e.toOpenPartialHomeomorph = ↑e
参数：e : Bundle.Trivialization F proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe : ⇑e.toOpenPartialHomeomorph = e :=
  rfl

@[simp, mfld_simps]
/-
**Bundle.Trivialization.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivialization
`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z}, x ∈ e.source → (↑e x).1 = proj x
参数：e : Bundle.Trivialization F proj；↑e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.proj_toFun`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : T
opologicalSpace Z] {pr…
-/
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_toFun x ex
/-
**Bundle.Trivialization.eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj), Set.EqOn (Prod.fst ∘ ↑e) proj e.source
参数：e : Bundle.Trivialization F proj；Prod.fst ∘ ↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
-/
protected theorem eqOn : EqOn (Prod.fst ∘ e) proj e.source := fun _x hx => e.coe_fst hx
/-
**Bundle.Trivialization.mem_source** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializat
ion`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z}, x ∈ e.source ↔ proj x ∈ e.baseSet
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_source : x ∈ e.source ↔ proj x ∈ e.baseSet := by rw [e.source_eq, mem_preimage]

@[simp, mfld_simps]
/-
**Bundle.Trivialization.coe_fst'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializatio
n`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z}, proj x ∈ e.baseSet → (↑e x).1 = proj x
参数：e : Bundle.Trivialization F proj；↑e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem coe_fst' (ex : proj x ∈ e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)
/-
**Bundle.Trivialization.mk_proj_snd** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializa
tion`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z}, x ∈ e.source → (proj x, (↑e x).2) = ↑e
 x
参数：e : Bundle.Trivialization F proj；proj x, (↑e x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
-/
theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl
/-
**Bundle.Trivialization.mk_proj_snd'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializ
ation`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z},   proj x ∈ e.baseSet → (proj x, (↑e x)
.2) = ↑e x
参数：e : Bundle.Trivialization F proj；proj x, (↑e x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.coe_fst'`：∀ {B : Type u_1} {F : Type u_2} {Z : Typ
e u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B} 
  [inst_2 : Topologi…
-/
theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl
/-
**Bundle.Trivialization.source_inter_preimage_target_inter** 是 Mathlib 中的一个定理，位于
命名空间 `Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) (s : Set (B × F)),   e.source ∩ ↑e ⁻¹' (e.targe
t ∩ s) = e.source ∩ ↑e ⁻¹' s
参数：e : Bundle.Trivialization F proj；s : Set (B × F)；e.target ∩ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.source_inter_preimage_target_inter`：source_inter_p
reimage_target_inter (s : Set Y) : e.source inter e ⁻¹' (e.target inter s) = e.s
ource inter e ⁻¹' s
-/
theorem source_inter_preimage_target_inter (s : Set (B × F)) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toOpenPartialHomeomorph.source_inter_preimage_target_inter s

@[simp, mfld_simps]
/-
**Bundle.Trivialization.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivialization`
。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : OpenPartialHomeomorph Z (B × F)) (i : Set B) (j : IsOpen i)   (k : e.source =
 proj ⁻¹' i) (l : e.target = i ×ˢ Set.univ) (m : ∀ p ∈ e.source, (↑e p).1 = proj
 p) (x : Z),   ↑{ toOpenPartialHomeomorph := e, baseSet := i, open_baseSet := j,
 source_eq := k, target_eq := l, proj_toFun := m }       x =     ↑e x
参数：e : OpenPartialHomeomorph Z (B × F)；i : Set B；j : IsOpen i；k : e.source = pro
j ⁻¹' i；l : e.target = i ×ˢ Set.univ；m : ∀ p ∈ e.source, (↑e p).1 = proj p；x : Z
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e : OpenPartialHomeomorph Z (B × F)) (i j k l m) (x : Z) :
    (Trivialization.mk e i j k l m : Trivialization F proj) x = e x :=
  rfl
/-
**Bundle.Trivialization.mem_target** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializat
ion`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : B × F}, x ∈ e.target ↔ x.1 ∈ e.baseSet
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.mem_target`：mem_target {x : B × F} : x in e.tar
get ↔ x.1 in e.baseSet
-/
theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.baseSet :=
  e.toPretrivialization.mem_target
/-
**Bundle.Trivialization.map_target** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializat
ion`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : B × F}, x ∈ e.target → ↑e.symm x ∈ e.sourc
e
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_target`：map_target {x : Y} (h : x in e.target)
 : e.symm x in e.source
-/
theorem map_target {x : B × F} (hx : x ∈ e.target) : e.toOpenPartialHomeomorph.symm x ∈ e.source :=
  e.toOpenPartialHomeomorph.map_target hx
/-
**Bundle.Trivialization.proj_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : B × F}, x ∈ e.target → proj (↑e.symm x) = 
x.1
参数：e : Bundle.Trivialization F proj；↑e.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply`：proj_symm_apply {x : B × F} (h
x : x in e.target) : proj (e.toPartialEquiv.symm x) = x.1
-/
theorem proj_symm_apply {x : B × F} (hx : x ∈ e.target) :
    proj (e.toOpenPartialHomeomorph.symm x) = x.1 :=
  e.toPretrivialization.proj_symm_apply hx
/-
**Bundle.Trivialization.proj_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {b : B} {x : F},   b ∈ e.baseSet → proj (↑e.sym
m (b, x)) = b
参数：e : Bundle.Trivialization F proj；↑e.symm (b, x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply'`：proj_symm_apply' {b : B} {x :
 F} (hx : b in e.baseSet) : proj (e.toPartialEquiv.symm (b, x)) = b
-/
theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    proj (e.toOpenPartialHomeomorph.symm (b, x)) = b :=
  e.toPretrivialization.proj_symm_apply' hx
/-
**Bundle.Trivialization.proj_surjOn_baseSet** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Tr
ivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) [Nonempty F], Set.SurjOn proj e.source e.baseSe
t
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.proj_surjOn_baseSet`：proj_surjOn_baseSet [Nonem
pty F] : Set.SurjOn proj e.source e.baseSet
-/
theorem proj_surjOn_baseSet [Nonempty F] : Set.SurjOn proj e.source e.baseSet :=
  e.toPretrivialization.proj_surjOn_baseSet

@[simp, mfld_simps]
/-
**Bundle.Trivialization.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : B × F}, x ∈ e.target → ↑e (↑e.symm x) = x
参数：e : Bundle.Trivialization F proj；↑e.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
-/
theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) :
    e (e.toOpenPartialHomeomorph.symm x) = x :=
  e.toOpenPartialHomeomorph.right_inv hx

@[simp, mfld_simps]
/-
**Bundle.Trivialization.apply_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {b : B} {x : F},   b ∈ e.baseSet → ↑e (↑e.symm 
(b, x)) = (b, x)
参数：e : Bundle.Trivialization F proj；↑e.symm (b, x)；b, x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.apply_symm_apply'`：apply_symm_apply' {b : B} {x
 : F} (hx : b in e.baseSet) : e (e.toPartialEquiv.symm (b, x)) = (b, x)
-/
theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    e (e.toOpenPartialHomeomorph.symm (b, x)) = (b, x) :=
  e.toPretrivialization.apply_symm_apply' hx

@[simp, mfld_simps]
/-
**Bundle.Trivialization.symm_apply_mk_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Tri
vialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z},   x ∈ e.source → ↑e.symm (proj x, (↑e 
x).2) = x
参数：e : Bundle.Trivialization F proj；proj x, (↑e x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.symm_apply_mk_proj`：symm_apply_mk_proj {x : Z} 
(ex : x in e.source) : e.toPartialEquiv.symm (proj x, (e x).2) = x
-/
theorem symm_apply_mk_proj (ex : x ∈ e.source) :
    e.toOpenPartialHomeomorph.symm (proj x, (e x).2) = x :=
  e.toPretrivialization.symm_apply_mk_proj ex
/-
**Bundle.Trivialization.symm_trans_source_eq** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.T
rivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 e' : Bundle.Trivialization F proj),   (e.symm.trans e'.toPartialEquiv).source =
 (e.baseSet ∩ e'.baseSet) ×ˢ Set.univ
参数：e e' : Bundle.Trivialization F proj；e.symm.trans e'.toPartialEquiv；e.baseSet 
∩ e'.baseSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.symm_trans_source_eq`：symm_trans_source_eq (e e
' : Pretrivialization F proj) : (e.toPartialEquiv.symm.trans e'.toPartialEquiv).
source = (e.baseSet inter e'.baseSe…
-/
theorem symm_trans_source_eq (e e' : Trivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).source = (e.baseSet ∩ e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_source_eq e.toPretrivialization e'
/-
**Bundle.Trivialization.symm_trans_target_eq** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.T
rivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 e' : Bundle.Trivialization F proj),   (e.symm.trans e'.toPartialEquiv).target =
 (e.baseSet ∩ e'.baseSet) ×ˢ Set.univ
参数：e e' : Bundle.Trivialization F proj；e.symm.trans e'.toPartialEquiv；e.baseSet 
∩ e'.baseSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.symm_trans_target_eq`：symm_trans_target_eq (e e
' : Pretrivialization F proj) : (e.toPartialEquiv.symm.trans e'.toPartialEquiv).
target = (e.baseSet inter e'.baseSe…
-/
theorem symm_trans_target_eq (e e' : Trivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).target = (e.baseSet ∩ e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_target_eq e.toPretrivialization e'
/-
**Bundle.Trivialization.coe_fst_eventuallyEq_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bun
dle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z}, x ∈ e.source → Prod.fst ∘ ↑e =ᶠ[nhds x
] proj
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem coe_fst_eventuallyEq_proj (ex : x ∈ e.source) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  mem_nhds_iff.2 ⟨e.source, fun _y hy => e.coe_fst hy, e.open_source, ex⟩
/-
**Bundle.Trivialization.coe_fst_eventuallyEq_proj'** 是 Mathlib 中的一个定理，位于命名空间 `Bu
ndle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z},   proj x ∈ e.baseSet → Prod.fst ∘ ↑e =
ᶠ[nhds x] proj
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.coe_fst_eventuallyEq_proj`：∀ {B : Type u_1} {F : T
ype u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
] {proj : Z → B}   [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem coe_fst_eventuallyEq_proj' (ex : proj x ∈ e.baseSet) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  e.coe_fst_eventuallyEq_proj (e.mem_source.2 ex)
/-
**Bundle.Trivialization.map_proj_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triviali
zation`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z},   x ∈ e.source → Filter.map proj (nhds
 x) = nhds (proj x)
参数：e : Bundle.Trivialization F proj；nhds x；proj x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `Filter.map_congr`：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f
] m₂) : map m₁ f = map m₂ f
· 使用定理 `Bundle.Trivialization.coe_fst_eventuallyEq_proj`：∀ {B : Type u_1} {F : T
ype u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F
] {proj : Z → B}   [inst_2 : Topologi…
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Bundle.Trivialization.coe_coe`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `OpenPartialHomeomorph.map_nhds_eq`：map_nhds_eq {x} (hx : x in e.source) 
: map e (𝓝 x) = 𝓝 (e x)
· 使用定理 `map_fst_nhds`：map_fst_nhds (x : X × Y) : map Prod.fst (𝓝 x) = 𝓝 x.1
-/
theorem map_proj_nhds (ex : x ∈ e.source) : map proj (𝓝 x) = 𝓝 (proj x) := by
  rw [← e.coe_fst ex, ← map_congr (e.coe_fst_eventuallyEq_proj ex), ← map_map, ← e.coe_coe,
    e.map_nhds_eq ex, map_fst_nhds]
/-
**Bundle.Trivialization.preimage_subset_source** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {s : Set B}, s ⊆ e.baseSet → proj ⁻¹' s ⊆ e.sou
rce
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem preimage_subset_source {s : Set B} (hb : s ⊆ e.baseSet) : proj ⁻¹' s ⊆ e.source :=
  fun _p hp => e.mem_source.mpr (hb hp)
/-
**Bundle.Trivialization.image_preimage_eq_prod_univ** 是 Mathlib 中的一个定理，位于命名空间 `B
undle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {s : Set B},   s ⊆ e.baseSet → ↑e '' proj ⁻¹' s
 = s ×ˢ Set.univ
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.proj_toFun`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : T
opologicalSpace Z] {pr…
· 使用定理 `Bundle.Trivialization.preimage_subset_source`：∀ {B : Type u_1} {F : Type
 u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {
proj : Z → B}   [inst_2 : Topologi…
· 使用定理 `trivial`：True
· 使用定理 `Bundle.Trivialization.mem_target`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Bundle.Trivialization.proj_symm_apply`：∀ {B : Type u_1} {F : Type u_2} {
Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : 
Z → B}   [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.apply_symm_apply`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
-/
theorem image_preimage_eq_prod_univ {s : Set B} (hb : s ⊆ e.baseSet) :
    e '' proj ⁻¹' s = s ×ˢ univ :=
  Subset.antisymm
    (image_subset_iff.mpr fun p hp =>
      ⟨(e.proj_toFun p (e.preimage_subset_source hb hp)).symm ▸ hp, trivial⟩)
    fun p hp =>
    let hp' : p ∈ e.target := e.mem_target.mpr (hb hp.1)
    ⟨e.invFun p, mem_preimage.mpr ((e.proj_symm_apply hp').symm ▸ hp.1), e.apply_symm_apply hp'⟩
/-
**Bundle.Trivialization.tendsto_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {α : Type u_5} {l : Filter α} {f : α → Z} {z : 
Z},   z ∈ e.source →     (Filter.Tendsto f l (nhds z) ↔       Filter.Tendsto (pr
oj ∘ f) l (nhds (proj z)) ∧ Filter.Tendsto (fun x => (↑e (f x)).2) l (nhds (↑e z
).2))
参数：e : Bundle.Trivialization F proj；Filter.Tendsto f l (nhds z) ↔       Filter.T
endsto (proj ∘ f) l (nhds (proj z)) ∧ Filter.Tendsto (fun x => (↑e (f x)).2) l (
nhds (↑e z).2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.nhds_eq_comap_inf_principal`：nhds_eq_comap_inf_pri
ncipal {x} (hx : x in e.source) : 𝓝 x = comap e (𝓝 (e x)) ⊓ 𝓟 e.source
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Prod.tendsto_iff`：Prod.tendsto_iff {X} (seq : X -> Y × Z) {f : Filter X}
 (p : Y × Z) : Tendsto seq f (𝓝 p) ↔ Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) 
∧ Tend…
· 使用定理 `Bundle.Trivialization.coe_coe`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
-/
theorem tendsto_nhds_iff {α : Type*} {l : Filter α} {f : α → Z} {z : Z} (hz : z ∈ e.source) :
    Tendsto f l (𝓝 z) ↔
      Tendsto (proj ∘ f) l (𝓝 (proj z)) ∧ Tendsto (fun x ↦ (e (f x)).2) l (𝓝 (e z).2) := by
  rw [e.nhds_eq_comap_inf_principal hz, tendsto_inf, tendsto_comap_iff, Prod.tendsto_iff, coe_coe,
    tendsto_principal, coe_fst _ hz]
  by_cases hl : ∀ᶠ x in l, f x ∈ e.source
  · simp only [hl, and_true]
    refine (tendsto_congr' ?_).and Iff.rfl
    exact hl.mono fun x ↦ e.coe_fst
  · simp only [hl, and_false, false_iff, not_and]
    rw [e.source_eq] at hl hz
    exact fun h _ ↦ hl <| h <| e.open_baseSet.mem_nhds hz
/-
**Bundle.Trivialization.nhds_eq_inf_comap** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {z : Z},   z ∈ e.source → nhds z = Filter.comap
 proj (nhds (proj z)) ⊓ Filter.comap (Prod.snd ∘ ↑e) (nhds (↑e z).2)
参数：e : Bundle.Trivialization F proj；nhds (proj z)；Prod.snd ∘ ↑e；nhds (↑e z).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `Bundle.Trivialization.tendsto_nhds_iff`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
-/
theorem nhds_eq_inf_comap {z : Z} (hz : z ∈ e.source) :
    𝓝 z = comap proj (𝓝 (proj z)) ⊓ comap (Prod.snd ∘ e) (𝓝 (e z).2) := by
  refine eq_of_forall_le_iff fun l ↦ ?_
  rw [le_inf_iff, ← tendsto_iff_comap, ← tendsto_iff_comap]
  exact e.tendsto_nhds_iff hz

/-- The preimage of a subset of the base set is homeomorphic to the product with the fiber. -/
/-
**Bundle.Trivialization.preimageHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Tri
vialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               (e : Bundle.Triv
ialization F proj) → {s : Set B} → s ⊆ e.baseSet → ↑(proj ⁻¹' s) ≃ₜ ↑s × F
参数：e : Bundle.Trivialization F proj；proj ⁻¹' s。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.preimage_subset_source`：∀ {B : Type u_1} {F : Type
 u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {
proj : Z → B}   [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.image_preimage_eq_prod_univ`：∀ {B : Type u_1} {F :
 Type u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace
 F] {proj : Z → B}   [inst_2 : Topologi…

--- 原说明 ---
The preimage of a subset of the base set is homeomorphic to the product with the
 fiber.
-/
def preimageHomeomorph {s : Set B} (hb : s ⊆ e.baseSet) : proj ⁻¹' s ≃ₜ s × F :=
  (e.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource (e.preimage_subset_source hb)
        (e.image_preimage_eq_prod_univ hb)).trans
    ((Homeomorph.Set.prod s univ).trans ((Homeomorph.refl s).prodCongr (Homeomorph.Set.univ F)))

@[simp]
/-
**Bundle.Trivialization.preimageHomeomorph_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bund
le.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {s : Set B} (hb : s ⊆ e.baseSet) (p : ↑(proj ⁻¹
' s)),   (e.preimageHomeomorph hb) p = (⟨proj ↑p, ⋯⟩, (↑e ↑p).2)
参数：e : Bundle.Trivialization F proj；hb : s ⊆ e.baseSet；p : ↑(proj ⁻¹' s)；e.preim
ageHomeomorph hb；⟨proj ↑p, ⋯⟩, (↑e ↑p).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Bundle.Trivialization.proj_toFun`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : T
opologicalSpace Z] {pr…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem preimageHomeomorph_apply {s : Set B} (hb : s ⊆ e.baseSet) (p : proj ⁻¹' s) :
    e.preimageHomeomorph hb p = (⟨proj p, p.2⟩, (e p).2) :=
  Prod.ext (Subtype.ext (e.proj_toFun p (e.mem_source.mpr (hb p.2)))) rfl

/-- Auxiliary definition to avoid looping in `dsimp`
with `Bundle.Trivialization.preimageHomeomorph_symm_apply`. -/
/-
**Bundle.Trivialization.preimageHomeomorph_symm_apply.aux** 是 Mathlib 中的一个定义，位于命
名空间 `Bundle.Trivialization.preimageHomeomorph_symm_apply`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               (e : Bundle.Triv
ialization F proj) → {s : Set B} → s ⊆ e.baseSet → ↑s × F ≃ₜ ↑(proj ⁻¹' s)
参数：e : Bundle.Trivialization F proj；proj ⁻¹' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to avoid looping in `dsimp`
with `Bundle.Trivialization.preimageHomeomorph_symm_apply`.
-/
protected def preimageHomeomorph_symm_apply.aux {s : Set B} (hb : s ⊆ e.baseSet) :=
  (e.preimageHomeomorph hb).symm

@[simp]
/-
**Bundle.Trivialization.preimageHomeomorph_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 
`Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {s : Set B} (hb : s ⊆ e.baseSet) (p : ↑s × F), 
  (e.preimageHomeomorph hb).symm p = ⟨↑e.symm (↑p.1, p.2), ⋯⟩
参数：e : Bundle.Trivialization F proj；hb : s ⊆ e.baseSet；p : ↑s × F；e.preimageHome
omorph hb；↑p.1, p.2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimageHomeomorph_symm_apply {s : Set B} (hb : s ⊆ e.baseSet) (p : s × F) :
    (e.preimageHomeomorph hb).symm p =
      ⟨e.symm (p.1, p.2), ((preimageHomeomorph_symm_apply.aux e hb) p).2⟩ :=
  rfl

/-- The source is homeomorphic to the product of the base set with the fiber. -/
/-
**Bundle.Trivialization.sourceHomeomorphBaseSetProd** 是 Mathlib 中的一个定义，位于命名空间 `B
undle.Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] → (e : Bundle.Trivialization F p
roj) → ↑e.source ≃ₜ ↑e.baseSet × F
参数：e : Bundle.Trivialization F proj。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…

--- 原说明 ---
The source is homeomorphic to the product of the base set with the fiber.
-/
def sourceHomeomorphBaseSetProd : e.source ≃ₜ e.baseSet × F :=
  (Homeomorph.setCongr e.source_eq).trans (e.preimageHomeomorph subset_rfl)

@[simp]
/-
**Bundle.Trivialization.sourceHomeomorphBaseSetProd_apply** 是 Mathlib 中的一个定理，位于命
名空间 `Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) (p : ↑e.source),   e.sourceHomeomorphBaseSetPro
d p = (⟨proj ↑p, ⋯⟩, (↑e ↑p).2)
参数：e : Bundle.Trivialization F proj；p : ↑e.source；⟨proj ↑p, ⋯⟩, (↑e ↑p).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.preimageHomeomorph_apply`：∀ {B : Type u_1} {F : Ty
pe u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]
 {proj : Z → B}   [inst_2 : Topologi…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem sourceHomeomorphBaseSetProd_apply (p : e.source) :
    e.sourceHomeomorphBaseSetProd p = (⟨proj p, e.mem_source.mp p.2⟩, (e p).2) :=
  e.preimageHomeomorph_apply subset_rfl ⟨p, e.mem_source.mp p.2⟩

/-- Auxiliary definition to avoid looping in `dsimp`
with `Bundle.Trivialization.sourceHomeomorphBaseSetProd_symm_apply`. -/
/-
**Bundle.Trivialization.sourceHomeomorphBaseSetProd_symm_apply.aux** 是 Mathlib 中
的一个定义，位于命名空间 `Bundle.Trivialization.sourceHomeomorphBaseSetProd_symm_apply`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] → (e : Bundle.Trivialization F p
roj) → ↑e.baseSet × F ≃ₜ ↑e.source
参数：e : Bundle.Trivialization F proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to avoid looping in `dsimp`
with `Bundle.Trivialization.sourceHomeomorphBaseSetProd_symm_apply`.
-/
protected def sourceHomeomorphBaseSetProd_symm_apply.aux := e.sourceHomeomorphBaseSetProd.symm

@[simp]
/-
**Bundle.Trivialization.sourceHomeomorphBaseSetProd_symm_apply** 是 Mathlib 中的一个定
理，位于命名空间 `Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) (p : ↑e.baseSet × F),   e.sourceHomeomorphBaseS
etProd.symm p = ⟨↑e.symm (↑p.1, p.2), ⋯⟩
参数：e : Bundle.Trivialization F proj；p : ↑e.baseSet × F；↑p.1, p.2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sourceHomeomorphBaseSetProd_symm_apply (p : e.baseSet × F) :
    e.sourceHomeomorphBaseSetProd.symm p =
      ⟨e.symm (p.1, p.2), (sourceHomeomorphBaseSetProd_symm_apply.aux e p).2⟩ :=
  rfl

/-- Each fiber of a trivialization is homeomorphic to the specified fiber. -/
/-
**Bundle.Trivialization.preimageSingletonHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `B
undle.Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               (e : Bundle.Triv
ialization F proj) → {b : B} → b ∈ e.baseSet → ↑(proj ⁻¹' {b}) ≃ₜ F
参数：e : Bundle.Trivialization F proj；proj ⁻¹' {b}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each fiber of a trivialization is homeomorphic to the specified fiber.
-/
def preimageSingletonHomeomorph {b : B} (hb : b ∈ e.baseSet) : proj ⁻¹' {b} ≃ₜ F :=
  .trans (e.preimageHomeomorph (Set.singleton_subset_iff.mpr hb)) <|
    .trans (.prodCongr (Homeomorph.homeomorphOfUnique ({b} : Set B) PUnit.{1}) (Homeomorph.refl F))
      (Homeomorph.punitProd F)

@[simp]
/-
**Bundle.Trivialization.preimageSingletonHomeomorph_apply** 是 Mathlib 中的一个定理，位于命
名空间 `Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) (p : ↑(proj ⁻¹' {b
})),   (e.preimageSingletonHomeomorph hb) p = (↑e ↑p).2
参数：e : Bundle.Trivialization F proj；hb : b ∈ e.baseSet；p : ↑(proj ⁻¹' {b})；e.pre
imageSingletonHomeomorph hb；↑e ↑p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimageSingletonHomeomorph_apply {b : B} (hb : b ∈ e.baseSet) (p : proj ⁻¹' {b}) :
    e.preimageSingletonHomeomorph hb p = (e p).2 :=
  rfl

@[simp]
/-
**Bundle.Trivialization.preimageSingletonHomeomorph_symm_apply** 是 Mathlib 中的一个定
理，位于命名空间 `Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) (p : F),   (e.prei
mageSingletonHomeomorph hb).symm p = ⟨↑e.symm (b, p), ⋯⟩
参数：e : Bundle.Trivialization F proj；hb : b ∈ e.baseSet；p : F；e.preimageSingleton
Homeomorph hb；b, p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimageSingletonHomeomorph_symm_apply {b : B} (hb : b ∈ e.baseSet) (p : F) :
    (e.preimageSingletonHomeomorph hb).symm p =
      ⟨e.symm (b, p), by rw [mem_preimage, e.proj_symm_apply' hb, mem_singleton_iff]⟩ :=
  rfl

/-- In the domain of a bundle trivialization, the projection is continuous -/
/-
**Bundle.Trivialization.continuousAt_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {x : Z}, x ∈ e.source → ContinuousAt proj x
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Bundle.Trivialization.map_proj_nhds`：∀ {B : Type u_1} {F : Type u_2} {Z 
: Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z 
→ B}   [inst_2 : Topologi…

--- 原说明 ---
In the domain of a bundle trivialization, the projection is continuous
-/
theorem continuousAt_proj (ex : x ∈ e.source) : ContinuousAt proj x :=
  (e.map_proj_nhds ex).le
/-
**Bundle.Trivialization.continuousOn_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj), ContinuousOn proj e.source
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `Bundle.Trivialization.continuousAt_proj`：∀ {B : Type u_1} {F : Type u_2}
 {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj 
: Z → B}   [inst_2 : Topologi…
-/
theorem continuousOn_proj : ContinuousOn proj e.source :=
  continuousOn_of_forall_continuousAt fun _ ↦ e.continuousAt_proj

/-- For fixed `v ∈ F`, `x ↦ e.symm (x,v)` is continuous at any point in the base set. -/
/-
**Bundle.Trivialization.continuousAt_symm_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 
`Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {b : B} {v : F},   b ∈ e.baseSet → ContinuousAt
 (fun x => ↑e.symm (x, v)) b
参数：e : Bundle.Trivialization F proj；fun x => ↑e.symm (x, v)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `OpenPartialHomeomorph.continuousAt_symm`：continuousAt_symm {x : Y} (h : 
x in e.target) : ContinuousAt e.symm x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_target`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x

--- 原说明 ---
For fixed `v ∈ F`, `x ↦ e.symm (x,v)` is continuous at any point in the base set
.
-/
theorem continuousAt_symm_prodMk_left {b : B} {v : F} (hb : b ∈ e.baseSet) :
    ContinuousAt (fun x ↦ e.symm (x, v)) b :=
  (e.toOpenPartialHomeomorph.continuousAt_symm (e.mem_target.mpr hb)).comp (by fun_prop)

/-- For fixed `v ∈ F`, `x ↦ e.symm (x,v)` is continuous on `e.baseSet`. -/
/-
**Bundle.Trivialization.continuousOn_symm_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 
`Bundle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {v : F},   ContinuousOn (fun x => ↑e.symm (x, v
)) e.baseSet
参数：e : Bundle.Trivialization F proj；fun x => ↑e.symm (x, v)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Bundle.Trivialization.continuousAt_symm_prodMk_left`：∀ {B : Type u_1} {F
 : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpa
ce F] {proj : Z → B}   [inst_2 : Topologi…

--- 原说明 ---
For fixed `v ∈ F`, `x ↦ e.symm (x,v)` is continuous on `e.baseSet`.
-/
theorem continuousOn_symm_prodMk_left {v : F} : ContinuousOn (fun x ↦ e.symm (x, v)) e.baseSet :=
  fun _ hb ↦ (e.continuousAt_symm_prodMk_left hb).continuousWithinAt

/-- Pre-composition of a `Bundle.Trivialization` and a `Homeomorph`. -/
/-
**Bundle.Trivialization.compHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivial
ization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               Bundle.Trivializ
ation F proj →                 {Z' : Type u_5} → [inst_3 : TopologicalSpace Z'] 
→ (h : Z' ≃ₜ Z) → Bundle.Trivialization F (proj ∘ ⇑h)
参数：h : Z' ≃ₜ Z；proj ∘ ⇑h。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…

--- 原说明 ---
Pre-composition of a `Bundle.Trivialization` and a `Homeomorph`.
-/
protected def compHomeomorph {Z' : Type*} [TopologicalSpace Z'] (h : Z' ≃ₜ Z) :
    Trivialization F (proj ∘ h) where
  toOpenPartialHomeomorph := h.transOpenPartialHomeomorph e.toOpenPartialHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by simp [source_eq, preimage_preimage, Function.comp_def]
  target_eq := by simp [target_eq]
  proj_toFun p hp := by
    have hp : h p ∈ e.source := by simpa using hp
    simp [hp]

/-- Post-composition of a `Bundle.Trivialization` and a `Homeomorph`. -/
/-
**Bundle.Trivialization.homeomorphComp** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivial
ization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               Bundle.Trivializ
ation F proj →                 {B' : Type u_5} → [inst_3 : TopologicalSpace B'] 
→ (h : B ≃ₜ B') → Bundle.Trivialization F (⇑h ∘ proj)
参数：h : B ≃ₜ B'；⇑h ∘ proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Post-composition of a `Bundle.Trivialization` and a `Homeomorph`.
-/
protected def homeomorphComp {B' : Type*} [TopologicalSpace B'] (h : B ≃ₜ B') :
    Trivialization F (h ∘ proj) where
  toOpenPartialHomeomorph := e.toOpenPartialHomeomorph.transHomeomorph (h.prodCongr <| .refl _)
  baseSet := h.symm ⁻¹' e.baseSet
  open_baseSet := e.open_baseSet.preimage h.continuous_symm
  source_eq := by ext; simp [e.mem_source]
  target_eq := by ext; simp [Prod.map, e.mem_target]
  proj_toFun p hp := by simpa using e.proj_toFun p hp

/-- Read off the continuity of a function `f : Z → X` at `z : Z` by transferring via a
trivialization of `Z` containing `z`. -/
/-
**Bundle.Trivialization.continuousAt_of_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Bu
ndle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] {X
 : Type u_5} [inst_3 : TopologicalSpace X] {f : Z → X} {z : Z}   (e : Bundle.Tri
vialization F proj), proj z ∈ e.baseSet → ContinuousAt (f ∘ ↑e.symm) (↑e z) → Co
ntinuousAt f z
参数：e : Bundle.Trivialization F proj；f ∘ ↑e.symm；↑e z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.symm_target`：symm_target : e.symm.target = e.source
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_right`：continuo
usAt_iff_continuousAt_comp_right {f : Y -> Z} {x : Y} (h : x in e.target) : Cont
inuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x)
· 使用定理 `OpenPartialHomeomorph.symm_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), e.symm.symm = e

--- 原说明 ---
Read off the continuity of a function `f : Z → X` at `z : Z` by transferring via
 a
trivialization of `Z` containing `z`.
-/
theorem continuousAt_of_comp_right {X : Type*} [TopologicalSpace X] {f : Z → X} {z : Z}
    (e : Trivialization F proj) (he : proj z ∈ e.baseSet)
    (hf : ContinuousAt (f ∘ e.toPartialEquiv.symm) (e z)) : ContinuousAt f z := by
  have hez : z ∈ e.toPartialEquiv.symm.target := by
    rw [PartialEquiv.symm_target, e.mem_source]
    exact he
  rwa [e.toOpenPartialHomeomorph.symm.continuousAt_iff_continuousAt_comp_right hez,
    OpenPartialHomeomorph.symm_symm]

/-- Read off the continuity of a function `f : X → Z` at `x : X` by transferring via a
trivialization of `Z` containing `f x`. -/
/-
**Bundle.Trivialization.continuousAt_of_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Bun
dle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] {X
 : Type u_5} [inst_3 : TopologicalSpace X] {f : X → Z} {x : X}   (e : Bundle.Tri
vialization F proj),   ContinuousAt (proj ∘ f) x → proj (f x) ∈ e.baseSet → Cont
inuousAt (↑e ∘ f) x → ContinuousAt f x
参数：e : Bundle.Trivialization F proj；proj ∘ f；f x；↑e ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left`：continuou
sAt_iff_continuousAt_comp_left {f : Z -> X} {x : Z} (h : f ⁻¹' e.source in 𝓝 x) 
: ContinuousAt f x ↔ ContinuousAt (e ∘ f) x
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…

--- 原说明 ---
Read off the continuity of a function `f : X → Z` at `x : X` by transferring via
 a
trivialization of `Z` containing `f x`.
-/
theorem continuousAt_of_comp_left {X : Type*} [TopologicalSpace X] {f : X → Z} {x : X}
    (e : Trivialization F proj) (hf_proj : ContinuousAt (proj ∘ f) x) (he : proj (f x) ∈ e.baseSet)
    (hf : ContinuousAt (e ∘ f) x) : ContinuousAt f x := by
  rw [e.continuousAt_iff_continuousAt_comp_left]
  · exact hf
  rw [e.source_eq, ← preimage_comp]
  exact hf_proj.preimage_mem_nhds (e.open_baseSet.mem_nhds he)

variable (e' : Trivialization F (π F E)) {b : B} {y : E b}
/-
**Bundle.Trivialization.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializ
ation`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] (e' : Bundle.Trivialization F Bundle.TotalSpace.proj),   ContinuousOn (
↑e') e'.source
参数：Bundle.TotalSpace F E；e' : Bundle.Trivialization F Bundle.TotalSpace.proj；↑e'
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…
-/
protected theorem continuousOn : ContinuousOn e' e'.source :=
  e'.continuousOn_toFun
/-
**Bundle.Trivialization.coe_mem_source** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivial
ization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] (e' : Bundle.Trivialization F Bundle.TotalSpace.proj) {b : B}   {y : E 
b}, ⟨b, y⟩ ∈ e'.source ↔ b ∈ e'.baseSet
参数：Bundle.TotalSpace F E；e' : Bundle.Trivialization F Bundle.TotalSpace.proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.baseSet :=
  e'.mem_source
/-
**Bundle.Trivialization.coe_coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializa
tion`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] (e' : Bundle.Trivialization F Bundle.TotalSpace.proj) {b : B}   {y : E 
b}, b ∈ e'.baseSet → (↑e' ⟨b, y⟩).1 = b
参数：Bundle.TotalSpace F E；e' : Bundle.Trivialization F Bundle.TotalSpace.proj；↑e'
 ⟨b, y⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem coe_coe_fst (hb : b ∈ e'.baseSet) : (e' y).1 = b :=
  e'.coe_fst (e'.mem_source.2 hb)
/-
**Bundle.Trivialization.mk_mem_target** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triviali
zation`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] (e' : Bundle.Trivialization F Bundle.TotalSpace.proj) {b : B}   {y : F}
, (b, y) ∈ e'.target ↔ b ∈ e'.baseSet
参数：Bundle.TotalSpace F E；e' : Bundle.Trivialization F Bundle.TotalSpace.proj；b, 
y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.mem_target`：mem_target {x : B × F} : x in e.tar
get ↔ x.1 in e.baseSet
-/
theorem mk_mem_target {y : F} : (b, y) ∈ e'.target ↔ b ∈ e'.baseSet :=
  e'.toPretrivialization.mem_target

@[simp, mfld_simps]
/-
**Bundle.Trivialization.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] (e' : Bundle.Trivialization F Bundle.TotalSpace.proj)   {x : Bundle.Tot
alSpace F E}, x ∈ e'.source → ↑e'.symm (↑e' x) = x
参数：Bundle.TotalSpace F E；e' : Bundle.Trivialization F Bundle.TotalSpace.proj；↑e'
 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
-/
theorem symm_apply_apply {x : TotalSpace F E} (hx : x ∈ e'.source) :
    e'.toOpenPartialHomeomorph.symm (e' x) = x :=
  e'.toPartialEquiv.left_inv hx

@[simp, mfld_simps]
/-
**Bundle.Trivialization.symm_coe_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triviali
zation`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] {x : B} {y : F}   (e : Bundle.Trivialization F Bundle.TotalSpace.proj),
 x ∈ e.baseSet → (↑e.symm (x, y)).proj = x
参数：Bundle.TotalSpace F E；e : Bundle.Trivialization F Bundle.TotalSpace.proj；↑e.s
ymm (x, y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.proj_symm_apply'`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
-/
theorem symm_coe_proj {x : B} {y : F} (e : Trivialization F (π F E)) (h : x ∈ e.baseSet) :
    (e.toOpenPartialHomeomorph.symm (x, y)).1 = x :=
  e.proj_symm_apply' h

section Nonempty

variable [∀ x, Nonempty (E x)]

/-- A fiberwise inverse to `e'`. The function `F → E x` that induces a local inverse
`B × F → TotalSpace F E` of `e'` on `e'.baseSet`. It takes on junk values chosen using
`Classical.arbitrary` outside `e'.baseSet`. -/
/-
**Bundle.Trivialization.symm** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {E : B → Type u_3} →       [inst :
 TopologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2
 : TopologicalSpace (Bundle.TotalSpace F E)] →             [∀ (x : B), Nonempty 
(E x)] → Bundle.Trivialization F Bundle.TotalSpace.proj → (b : B) → F → E b
参数：Bundle.TotalSpace F E；x : B；E x；b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fiberwise inverse to `e'`. The function `F → E x` that induces a local inverse
`B × F → TotalSpace F E` of `e'` on `e'.baseSet`. It takes on junk values chosen
 using
`Classical.arbitrary` outside `e'.baseSet`.
-/
protected noncomputable def symm (e : Trivialization F (π F E)) (b : B) (y : F) : E b :=
  e.toPretrivialization.symm b y
/-
**Bundle.Trivialization.symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializat
ion`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] [inst_3 : ∀ (x : B), Nonempty (E x)]   (e : Bundle.Trivialization F Bun
dle.TotalSpace.proj) {b : B} (hb : b ∈ e.baseSet) (y : F),   e.symm b y = cast ⋯
 (↑e.symm (b, y)).snd
参数：Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization F Bundle.TotalSpace
.proj；hb : b ∈ e.baseSet；y : F；↑e.symm (b, y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem symm_apply (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e.symm b y =
      cast (congr_arg E (e.symm_coe_proj hb)) (e.toOpenPartialHomeomorph.symm (b, y)).2 :=
  dif_pos hb

@[deprecated "The junk values of `Trivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values." (since := "2026-06-23")]
/-
**Bundle.Trivialization.symm_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.T
rivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] [inst_3 : ∀ (x : B), Nonempty (E x)]   (e : Bundle.Trivialization F Bun
dle.TotalSpace.proj) {b : B},   b ∉ e.baseSet → ∀ (y : F), e.symm b y = Classica
l.arbitrary (E b)
参数：Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization F Bundle.TotalSpace
.proj；y : F；E b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.symm_apply_of_notMem`：symm_apply_of_notMem (e :
 Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) (y : F) : e.symm b y 
= Classical.arbitrary _
-/
theorem symm_apply_of_notMem (e : Trivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) (y : F) :
    e.symm b y = Classical.arbitrary _ :=
  e.toPretrivialization.symm_apply_of_notMem hb y
/-
**Bundle.Trivialization.mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivialization
`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] [inst_3 : ∀ (x : B), Nonempty (E x)]   (e : Bundle.Trivialization F Bun
dle.TotalSpace.proj) {b : B},   b ∈ e.baseSet → ∀ (y : F), ⟨b, e.symm b y⟩ = ↑e.
symm (b, y)
参数：Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization F Bundle.TotalSpace
.proj；y : F；b, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.mk_symm`：mk_symm (e : Pretrivialization F (π F 
E)) {b : B} (hb : b in e.baseSet) (y : F) : TotalSpace.mk b (e.symm b y) = e.toP
artialEquiv.symm (b, y…
-/
theorem mk_symm (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    TotalSpace.mk b (e.symm b y) = e.toOpenPartialHomeomorph.symm (b, y) :=
  e.toPretrivialization.mk_symm hb y

@[simp, mfld_simps]
/-
**Bundle.Trivialization.symm_proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] [inst_3 : ∀ (x : B), Nonempty (E x)]   (e : Bundle.Trivialization F Bun
dle.TotalSpace.proj) (z : Bundle.TotalSpace F E),   z.proj ∈ e.baseSet → e.symm 
z.proj (↑e z).2 = z.snd
参数：Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization F Bundle.TotalSpace
.proj；z : Bundle.TotalSpace F E；↑e z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.symm_proj_apply`：symm_proj_apply (e : Pretrivia
lization F (π F E)) (z : TotalSpace F E) (hz : z.proj in e.baseSet) : e.symm z.p
roj (e z).2 = z.2
-/
theorem symm_proj_apply (e : Trivialization F (π F E)) (z : TotalSpace F E)
    (hz : z.proj ∈ e.baseSet) : e.symm z.proj (e z).2 = z.2 :=
  e.toPretrivialization.symm_proj_apply z hz

@[simp, mfld_simps]
/-
**Bundle.Trivialization.symm_apply_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Tr
ivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] [inst_3 : ∀ (x : B), Nonempty (E x)]   (e : Bundle.Trivialization F Bun
dle.TotalSpace.proj) {b : B}, b ∈ e.baseSet → ∀ (y : E b), e.symm b (↑e ⟨b, y⟩).
2 = y
参数：Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization F Bundle.TotalSpace
.proj；y : E b；↑e ⟨b, y⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.symm_proj_apply`：∀ {B : Type u_1} {F : Type u_2} {
E : B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [i
nst_2 : TopologicalSpace (B…
-/
theorem symm_apply_apply_mk (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : E b) :
    e.symm b (e ⟨b, y⟩).2 = y :=
  e.symm_proj_apply ⟨b, y⟩ hb

@[simp, mfld_simps]
/-
**Bundle.Trivialization.apply_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triviali
zation`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] [inst_3 : ∀ (x : B), Nonempty (E x)]   (e : Bundle.Trivialization F Bun
dle.TotalSpace.proj) {b : B}, b ∈ e.baseSet → ∀ (y : F), ↑e ⟨b, e.symm b y⟩ = (b
, y)
参数：Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization F Bundle.TotalSpace
.proj；y : F；b, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.apply_mk_symm`：apply_mk_symm (e : Pretrivializa
tion F (π F E)) {b : B} (hb : b in e.baseSet) (y : F) : e ⟨b, e.symm b y⟩ = (b, 
y)
-/
theorem apply_mk_symm (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e ⟨b, e.symm b y⟩ = (b, y) :=
  e.toPretrivialization.apply_mk_symm hb y
/-
**Bundle.Trivialization.continuousOn_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {E : B → Type u_3} [inst : TopologicalSpac
e B] [inst_1 : TopologicalSpace F]   [inst_2 : TopologicalSpace (Bundle.TotalSpa
ce F E)] [inst_3 : ∀ (x : B), Nonempty (E x)]   (e : Bundle.Trivialization F Bun
dle.TotalSpace.proj),   ContinuousOn (fun z => ⟨z.1, e.symm z.1 z.2⟩) (e.baseSet
 ×ˢ Set.univ)
参数：Bundle.TotalSpace F E；x : B；E x；e : Bundle.Trivialization F Bundle.TotalSpace
.proj；fun z => ⟨z.1, e.symm z.1 z.2⟩；e.baseSet ×ˢ Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E : B → 
Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : 
TopologicalSpace (B…
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.target_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `OpenPartialHomeomorph.continuousOn_symm`：continuousOn_symm : ContinuousO
n e.symm e.target
-/
theorem continuousOn_symm (e : Trivialization F (π F E)) :
    ContinuousOn (fun z : B × F => TotalSpace.mk' F z.1 (e.symm z.1 z.2)) (e.baseSet ×ˢ univ) := by
  have : ∀ z ∈ e.baseSet ×ˢ (univ : Set F),
      TotalSpace.mk z.1 (e.symm z.1 z.2) = e.toOpenPartialHomeomorph.symm z := by
    rintro x ⟨hx : x.1 ∈ e.baseSet, _⟩
    rw [e.mk_symm hx]
  refine ContinuousOn.congr ?_ this
  rw [← e.target_eq]
  exact e.toOpenPartialHomeomorph.continuousOn_symm

end Nonempty

/-- If `e` is a `Trivialization` of `proj : Z → B` with fiber `F` and `h` is a homeomorphism
`F ≃ₜ F'`, then `e.trans_fiber_homeomorph h` is the trivialization of `proj` with the fiber `F'`
that sends `p : Z` to `((e p).1, h (e p).2)`. -/
/-
**Bundle.Trivialization.transFiberHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.T
rivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               {F' : Type u_5} 
→                 [inst_3 : TopologicalSpace F'] → Bundle.Trivialization F proj 
→ F ≃ₜ F' → Bundle.Trivialization F' proj
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Bundle.Trivialization.proj_toFun`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : T
opologicalSpace Z] {pr…

--- 原说明 ---
If `e` is a `Trivialization` of `proj : Z → B` with fiber `F` and `h` is a homeo
morphism
`F ≃ₜ F'`, then `e.trans_fiber_homeomorph h` is the trivialization of `proj` wit
h the fiber `F'`
that sends `p : Z` to `((e p).1, h (e p).2)`.
-/
def transFiberHomeomorph {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') : Trivialization F' proj where
  toOpenPartialHomeomorph :=
    e.toOpenPartialHomeomorph.transHomeomorph <| (Homeomorph.refl _).prodCongr h
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := by simp [target_eq, prod_univ, preimage_preimage]
  proj_toFun := e.proj_toFun

@[simp]
/-
**Bundle.Trivialization.transFiberHomeomorph_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bu
ndle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] {F
' : Type u_5} [inst_3 : TopologicalSpace F'] (e : Bundle.Trivialization F proj) 
  (h : F ≃ₜ F') (x : Z), ↑(e.transFiberHomeomorph h) x = ((↑e x).1, h (↑e x).2)
参数：e : Bundle.Trivialization F proj；h : F ≃ₜ F'；x : Z；e.transFiberHomeomorph h；(
↑e x).1, h (↑e x).2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transFiberHomeomorph_apply {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') (x : Z) : e.transFiberHomeomorph h x = ((e x).1, h (e x).2) :=
  rfl

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations. See also
`Bundle.Trivialization.coordChangeHomeomorph` for a version bundled as `F ≃ₜ F`. -/
/-
**Bundle.Trivialization.coordChange** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializa
tion`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] → Bundle.Trivialization F proj →
 Bundle.Trivialization F proj → B → F → F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coordinate transformation in the fiber induced by a pair of bundle trivializatio
ns. See also
`Bundle.Trivialization.coordChangeHomeomorph` for a version bundled as `F ≃ₜ F`.
-/
def coordChange (e₁ e₂ : Trivialization F proj) (b : B) (x : F) : F :=
  (e₂ <| e₁.toOpenPartialHomeomorph.symm (b, x)).2
/-
**Bundle.Trivialization.mk_coordChange** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivial
ization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
₁ e₂ : Bundle.Trivialization F proj) {b : B},   b ∈ e₁.baseSet → b ∈ e₂.baseSet 
→ ∀ (x : F), (b, e₁.coordChange e₂ b x) = ↑e₂ (↑e₁.symm (b, x))
参数：e₁ e₂ : Bundle.Trivialization F proj；x : F；b, e₁.coordChange e₂ b x；↑e₁.symm 
(b, x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coe_fst'`：∀ {B : Type u_1} {F : Type u_2} {Z : Typ
e u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B} 
  [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.proj_symm_apply'`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.apply_symm_apply'`：∀ {B : Type u_1} {F : Type u_2}
 {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj 
: Z → B}   [inst_2 : Topologi…
-/
theorem mk_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (x : F) :
    (b, e₁.coordChange e₂ b x) = e₂ (e₁.toOpenPartialHomeomorph.symm (b, x)) := by
  refine Prod.ext ?_ rfl
  rw [e₂.coe_fst', ← e₁.coe_fst', e₁.apply_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]

@[simp]
/-
**Bundle.Trivialization.coordChange_apply_snd** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.
Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
₁ e₂ : Bundle.Trivialization F proj) {p : Z},   proj p ∈ e₁.baseSet → e₁.coordCh
ange e₂ (proj p) (↑e₁ p).2 = (↑e₂ p).2
参数：e₁ e₂ : Bundle.Trivialization F proj；proj p；↑e₁ p；↑e₂ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coordChange.eq_1`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.symm_apply_mk_proj`：∀ {B : Type u_1} {F : Type u_2
} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj
 : Z → B}   [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem coordChange_apply_snd (e₁ e₂ : Trivialization F proj) {p : Z} (h : proj p ∈ e₁.baseSet) :
    e₁.coordChange e₂ (proj p) (e₁ p).snd = (e₂ p).snd := by
  rw [coordChange, e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]

@[simp, mfld_simps]
/-
**Bundle.Trivialization.coordChange_same_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {b : B},   b ∈ e.baseSet → ∀ (x : F), e.coordCh
ange e b x = x
参数：e : Bundle.Trivialization F proj；x : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coordChange.eq_1`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.apply_symm_apply'`：∀ {B : Type u_1} {F : Type u_2}
 {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj 
: Z → B}   [inst_2 : Topologi…
-/
theorem coordChange_same_apply (e : Trivialization F proj) {b : B} (h : b ∈ e.baseSet) (x : F) :
    e.coordChange e b x = x := by rw [coordChange, e.apply_symm_apply' h]
/-
**Bundle.Trivialization.coordChange_same** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) {b : B}, b ∈ e.baseSet → e.coordChange e b = id
参数：e : Bundle.Trivialization F proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bundle.Trivialization.coordChange_same_apply`：∀ {B : Type u_1} {F : Type
 u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {
proj : Z → B}   [inst_2 : Topologi…
-/
theorem coordChange_same (e : Trivialization F proj) {b : B} (h : b ∈ e.baseSet) :
    e.coordChange e b = id :=
  funext <| e.coordChange_same_apply h
/-
**Bundle.Trivialization.coordChange_coordChange** 是 Mathlib 中的一个定理，位于命名空间 `Bundl
e.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
₁ e₂ e₃ : Bundle.Trivialization F proj) {b : B},   b ∈ e₁.baseSet → b ∈ e₂.baseS
et → ∀ (x : F), e₂.coordChange e₃ b (e₁.coordChange e₂ b x) = e₁.coordChange e₃ 
b x
参数：e₁ e₂ e₃ : Bundle.Trivialization F proj；x : F；e₁.coordChange e₂ b x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coordChange.eq_1`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.mk_coordChange`：∀ {B : Type u_1} {F : Type u_2} {Z
 : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z
 → B}   [inst_2 : Topologi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.coe_coe`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.proj_symm_apply'`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
-/
theorem coordChange_coordChange (e₁ e₂ e₃ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (x : F) :
    e₂.coordChange e₃ b (e₁.coordChange e₂ b x) = e₁.coordChange e₃ b x := by
  rw [coordChange, e₁.mk_coordChange _ h₁ h₂, ← e₂.coe_coe, e₂.left_inv, coordChange]
  rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]
/-
**Bundle.Trivialization.continuous_coordChange** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
₁ e₂ : Bundle.Trivialization F proj) {b : B},   b ∈ e₁.baseSet → b ∈ e₂.baseSet 
→ Continuous (e₁.coordChange e₂ b)
参数：e₁ e₂ : Bundle.Trivialization F proj；e₁.coordChange e₂ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
· 使用定理 `OpenPartialHomeomorph.continuousOn_symm`：continuousOn_symm : ContinuousO
n e.symm e.target
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_target`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.proj_symm_apply'`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
-/
theorem continuous_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : Continuous (e₁.coordChange e₂ b) := by
  refine continuous_snd.comp (e₂.toOpenPartialHomeomorph.continuousOn.comp_continuous
    (e₁.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous ?_ ?_) ?_)
  · fun_prop
  · exact fun x => e₁.mem_target.2 h₁
  · intro x
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations,
as a homeomorphism. -/
/-
**Bundle.Trivialization.coordChangeHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.
Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               (e₁ e₂ : Bundle.
Trivialization F proj) → {b : B} → b ∈ e₁.baseSet → b ∈ e₂.baseSet → F ≃ₜ F
参数：e₁ e₂ : Bundle.Trivialization F proj。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.continuous_coordChange`：∀ {B : Type u_1} {F : Type
 u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {
proj : Z → B}   [inst_2 : Topologi…

--- 原说明 ---
Coordinate transformation in the fiber induced by a pair of bundle trivializatio
ns,
as a homeomorphism.
-/
protected def coordChangeHomeomorph (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : F ≃ₜ F where
  toFun := e₁.coordChange e₂ b
  invFun := e₂.coordChange e₁ b
  left_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  right_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  continuous_toFun := e₁.continuous_coordChange e₂ h₁ h₂
  continuous_invFun := e₂.continuous_coordChange e₁ h₂ h₁

@[simp]
/-
**Bundle.Trivialization.coordChangeHomeomorph_coe** 是 Mathlib 中的一个定理，位于命名空间 `Bun
dle.Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
₁ e₂ : Bundle.Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)   (h₂ : b ∈ e
₂.baseSet), ⇑(e₁.coordChangeHomeomorph e₂ h₁ h₂) = e₁.coordChange e₂ b
参数：e₁ e₂ : Bundle.Trivialization F proj；h₁ : b ∈ e₁.baseSet；h₂ : b ∈ e₂.baseSet；
e₁.coordChangeHomeomorph e₂ h₁ h₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coordChangeHomeomorph_coe (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : ⇑(e₁.coordChangeHomeomorph e₂ h₁ h₂) = e₁.coordChange e₂ b :=
  rfl
/-
**Bundle.Trivialization.isImage_preimage_prod** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.
Trivialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) (s : Set B), e.IsImage (proj ⁻¹' s) (s ×ˢ Set.u
niv)
参数：e : Bundle.Trivialization F proj；s : Set B；proj ⁻¹' s；s ×ˢ Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isImage_preimage_prod (e : Trivialization F proj) (s : Set B) :
    e.toOpenPartialHomeomorph.IsImage (proj ⁻¹' s) (s ×ˢ univ) := fun x hx => by simp [hx]

/-- Restrict a `Trivialization` to an open set in the base. -/
/-
**Bundle.Trivialization.restrOpen** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializati
on`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               Bundle.Trivializ
ation F proj → (s : Set B) → IsOpen s → Bundle.Trivialization F proj
参数：s : Set B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a `Trivialization` to an open set in the base.
-/
protected def restrOpen (e : Trivialization F proj) (s : Set B) (hs : IsOpen s) :
    Trivialization F proj where
  toOpenPartialHomeomorph :=
    ((e.isImage_preimage_prod s).symm.restr (IsOpen.inter e.open_target (hs.prod isOpen_univ))).symm
  baseSet := e.baseSet ∩ s
  open_baseSet := IsOpen.inter e.open_baseSet hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p hp := e.proj_toFun p hp.1

/-- The restriction of a trivialization to a subset of the base. -/
@[simps! apply source target baseSet]
/-
**Bundle.Trivialization.restrictPreimage'** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               Bundle.Trivializ
ation F proj →                 (s : Set B) → [Nonempty (↑s → F → ↑(proj ⁻¹' s))]
 → Bundle.Trivialization F (s.restrictPreimage proj)
参数：s : Set B；↑s → F → ↑(proj ⁻¹' s)；s.restrictPreimage proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a trivialization to a subset of the base.
-/
noncomputable def restrictPreimage' (e : Trivialization F proj) (s : Set B)
    [Nonempty (s → F → proj ⁻¹' s)] : Trivialization F (s.restrictPreimage proj) where
  __ := e.toPretrivialization.restrictPreimage' s
  open_source := e.open_source.preimage <| by fun_prop
  continuousOn_toFun := (Topology.IsInducing.subtypeVal.prodMap .id).continuousOn_iff.mpr <|
    (e.continuousOn_toFun.comp continuous_subtype_val.continuousOn fun _ ↦ id).congr
      fun z hz ↦ by ext; exacts [(e.proj_toFun _ hz).symm, rfl]
  continuousOn_invFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr <|
    (e.continuousOn_invFun.comp (continuous_subtype_val.prodMap continuous_id).continuousOn
      fun _ ↦ id).congr fun x hx ↦ congr_arg Subtype.val (dif_pos hx)

/-- The restriction of a trivialization to a set with nonempty intersection with the base set. -/
@[simps! apply source target baseSet]
/-
**Bundle.Trivialization.restrictPreimage** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               (e : Bundle.Triv
ialization F proj) →                 {s : Set B} → (s ∩ e.baseSet).Nonempty → Bu
ndle.Trivialization F (s.restrictPreimage proj)
参数：e : Bundle.Trivialization F proj；s ∩ e.baseSet；s.restrictPreimage proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a trivialization to a set with nonempty intersection with the
 base set.
-/
noncomputable def restrictPreimage (e : Trivialization F proj) {s : Set B}
    (hs : (s ∩ e.baseSet).Nonempty) : Trivialization F (s.restrictPreimage proj) :=
  have : Nonempty (F → proj ⁻¹' s) := .intro fun f ↦ Nonempty.some <| have ⟨z, hzs, hzb⟩ := hs
    ⟨⟨e.invFun ⟨z, f⟩, Set.mem_preimage.mpr <| (e.proj_symm_apply' hzb).symm ▸ hzs⟩⟩
  e.restrictPreimage' s

/-- Extend the total space of a trivialization from the preimage of a set to the whole space. -/
@[simps! symm_apply source target baseSet]
/-
**Bundle.Trivialization.domExtend** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializati
on`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               {s : Set B} →   
              IsOpen (proj ⁻¹' s) →                   (Bundle.Trivialization F f
un z => proj ↑z) → [Nonempty (Z → F)] → Bundle.Trivialization F proj
参数：proj ⁻¹' s；Bundle.Trivialization F fun z => proj ↑z；Z → F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Pretrivialization.open_target`：∀ {B : Type u_1} {F : Type u_2} {Z
 : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z
 → B}   (self : Bundle.Pre…
· 使用定理 `Bundle.Pretrivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {
Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : 
Z → B}   (self : Bundle.Pre…
· 使用定理 `Bundle.Pretrivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `Bundle.Pretrivialization.target_eq`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z →
 B}   (self : Bundle.Pre…
· 使用定理 `Bundle.Pretrivialization.proj_toFun`：∀ {B : Type u_1} {F : Type u_2} {Z 
: Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z 
→ B}   (self : Bundle.Pre…

--- 原说明 ---
Extend the total space of a trivialization from the preimage of a set to the who
le space.
-/
noncomputable def domExtend {s : Set B} (hps : IsOpen (proj ⁻¹' s))
    (e : Trivialization F fun z : proj ⁻¹' s ↦ proj z) [Nonempty (Z → F)] :
    Trivialization F proj where
  __ := e.toPretrivialization.domExtend
  open_source := hps.isOpenMap_subtype_val _ e.open_source
  continuousOn_toFun := Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr <| by
    convert! e.continuousOn_toFun
    ext1 ⟨x, (hx : proj x ∈ s)⟩
    simpa [Pretrivialization.domExtend] using! dif_pos hx
  continuousOn_invFun := continuous_subtype_val.comp_continuousOn <| by
    convert! e.continuousOn_invFun

/-- Extend the base of a trivialization from a set to the whole space. -/
@[simps! apply source target baseSet]
/-
**Bundle.Trivialization.codExtend'** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializat
ion`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2 : T
opologicalSpace Z] →             {s : Set B} →               IsOpen s →         
        {proj : Z → ↑s} →                   Bundle.Trivialization F proj → [None
mpty (B → F → Z)] → Bundle.Trivialization F (Subtype.val ∘ proj)
参数：B → F → Z；Subtype.val ∘ proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the base of a trivialization from a set to the whole space.
-/
noncomputable def codExtend' {s : Set B} (hs : IsOpen s) {proj : Z → s} (e : Trivialization F proj)
    [Nonempty (B → F → Z)] : Trivialization F (Subtype.val ∘ proj) where
  __ := e.toPretrivialization.codExtend' hs
  open_source := e.open_source
  continuousOn_toFun :=
    (continuous_subtype_val.prodMap continuous_id).comp_continuousOn e.continuousOn_toFun
  continuousOn_invFun := (Topology.IsInducing.subtypeVal.prodMap .id).continuousOn_image_iff.2 <| by
    convert! e.continuousOn_invFun; ext; simp [Pretrivialization.codExtend']; rfl

/-- Extend the base of a pretrivialization from a nonempty set to the whole space. -/
@[simps! apply source target baseSet]
/-
**Bundle.Trivialization.codExtend** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializati
on`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           [inst_2 : T
opologicalSpace Z] →             {s : Set B} →               IsOpen s →         
        s.Nonempty →                   {proj : Z → ↑s} → Bundle.Trivialization F
 proj → Bundle.Trivialization F (Subtype.val ∘ proj)
参数：Subtype.val ∘ proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the base of a pretrivialization from a nonempty set to the whole space.
-/
noncomputable def codExtend {s : Set B} (hs : IsOpen s) (nonempty : s.Nonempty) {proj : Z → s}
    (e : Trivialization F proj) : Trivialization F (Subtype.val ∘ proj) :=
  have : Nonempty (F → Z) := .intro fun f ↦ e.invFun (⟨_, nonempty.some_mem⟩, f)
  e.codExtend' hs

section Piecewise

/-
**Bundle.Trivialization.frontier_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triv
ialization`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] (e
 : Bundle.Trivialization F proj) (s : Set B),   e.source ∩ frontier (proj ⁻¹' s)
 = proj ⁻¹' (e.baseSet ∩ frontier s)
参数：e : Bundle.Trivialization F proj；s : Set B；proj ⁻¹' s；e.baseSet ∩ frontier s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.IsImage.preimage_eq`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialH
omeomorph X Y} {s : Set X} {t :…
· 使用定理 `OpenPartialHomeomorph.IsImage.frontier`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e : OpenPartialHome
omorph X Y} {s : Set X} {t :…
· 使用定理 `Bundle.Trivialization.isImage_preimage_prod`：∀ {B : Type u_1} {F : Type 
u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {p
roj : Z → B}   [inst_2 : Topologi…
· 使用定理 `frontier_prod_univ_eq`：frontier_prod_univ_eq (s : Set X) : frontier (s ×
ˢ (univ : Set Y)) = frontier s ×ˢ univ
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
-/
theorem frontier_preimage (e : Trivialization F proj) (s : Set B) :
    e.source ∩ frontier (proj ⁻¹' s) = proj ⁻¹' (e.baseSet ∩ frontier s) := by
  rw [← (e.isImage_preimage_prod s).frontier.preimage_eq, frontier_prod_univ_eq,
    (e.isImage_preimage_prod _).preimage_eq, e.source_eq, preimage_inter]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- Given two bundle trivializations `e`, `e'` of `proj : Z → B` and a set `s : Set B` such that
the base sets of `e` and `e'` intersect `frontier s` on the same set and `e p = e' p` whenever
`proj p ∈ e.baseSet ∩ frontier s`, `e.piecewise e' s Hs Heq` is the bundle trivialization over
`Set.ite s e.baseSet e'.baseSet` that is equal to `e` on `proj ⁻¹ s` and is equal to `e'`
otherwise. -/
/-
**Bundle.Trivialization.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializati
on`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               (e e' : Bundle.T
rivialization F proj) →                 (s : Set B) →                   e.baseSe
t ∩ frontier s = e'.baseSet ∩ frontier s →                     Set.EqOn (↑e) (↑e
') (proj ⁻¹' (e.baseSet ∩ frontier s)) → Bundle.Trivialization F proj
参数：e e' : Bundle.Trivialization F proj；s : Set B；↑e；↑e'；proj ⁻¹' (e.baseSet ∩ fr
ontier s)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.isImage_preimage_prod`：∀ {B : Type u_1} {F : Type 
u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {p
roj : Z → B}   [inst_2 : Topologi…

--- 原说明 ---
Given two bundle trivializations `e`, `e'` of `proj : Z → B` and a set `s : Set 
B` such that
the base sets of `e` and `e'` intersect `frontier s` on the same set and `e p = 
e' p` whenever
`proj p ∈ e.baseSet ∩ frontier s`, `e.piecewise e' s Hs Heq` is the bundle trivi
alization over
`Set.ite s e.baseSet e'.baseSet` that is equal to `e` on `proj ⁻¹ s` and is equa
l to `e'`
otherwise.
-/
noncomputable def piecewise (e e' : Trivialization F proj) (s : Set B)
    (Hs : e.baseSet ∩ frontier s = e'.baseSet ∩ frontier s)
    (Heq : EqOn e e' <| proj ⁻¹' (e.baseSet ∩ frontier s)) : Trivialization F proj where
  toOpenPartialHomeomorph :=
    e.toOpenPartialHomeomorph.piecewise e'.toOpenPartialHomeomorph (proj ⁻¹' s) (s ×ˢ univ)
      (e.isImage_preimage_prod s) (e'.isImage_preimage_prod s)
      (by rw [e.frontier_preimage, e'.frontier_preimage, Hs]) (by rwa [e.frontier_preimage])
  baseSet := s.ite e.baseSet e'.baseSet
  open_baseSet := e.open_baseSet.ite e'.open_baseSet Hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p := by
    rintro (⟨he, hs⟩ | ⟨he, hs⟩) <;> simp [*]

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B`
over a linearly ordered base `B` and a point `a ∈ e.baseSet ∩ e'.baseSet` such that
`e` equals `e'` on `proj ⁻¹' {a}`, `e.piecewise_le_of_eq e' a He He' Heq` is the bundle
trivialization over `Set.ite (Iic a) e.baseSet e'.baseSet` that is equal to `e` on points `p`
such that `proj p ≤ a` and is equal to `e'` otherwise. -/
/-
**Bundle.Trivialization.piecewiseLeOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               [inst_3 : Linear
Order B] →                 [OrderTopology B] →                   (e e' : Bundle.
Trivialization F proj) →                     (a : B) →                       a ∈
 e.baseSet →                         a ∈ e'.baseSet → (∀ (p : Z), proj p = a → ↑
e p = ↑e' p) → Bundle.Trivialization F proj
参数：e e' : Bundle.Trivialization F proj；a : B；∀ (p : Z), proj p = a → ↑e p = ↑e' 
p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj :
 Z → B`
over a linearly ordered base `B` and a point `a ∈ e.baseSet ∩ e'.baseSet` such t
hat
`e` equals `e'` on `proj ⁻¹' {a}`, `e.piecewise_le_of_eq e' a He He' Heq` is the
 bundle
trivialization over `Set.ite (Iic a) e.baseSet e'.baseSet` that is equal to `e` 
on points `p`
such that `proj p ≤ a` and is equal to `e'` otherwise.
-/
noncomputable def piecewiseLeOfEq [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) (Heq : ∀ p, proj p = a → e p = e' p) :
    Trivialization F proj :=
  e.piecewise e' (Iic a)
    (Set.ext fun x => and_congr_left_iff.2 fun hx => by
      obtain rfl : x = a := mem_singleton_iff.1 (frontier_Iic_subset _ hx)
      simp [He, He'])
    fun p hp => Heq p <| frontier_Iic_subset _ hp.2

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B` over a
linearly ordered base `B` and a point `a ∈ e.baseSet ∩ e'.baseSet`, `e.piecewise_le e' a He He'`
is the bundle trivialization over `Set.ite (Iic a) e.baseSet e'.baseSet` that is equal to `e` on
points `p` such that `proj p ≤ a` and is equal to `((e' p).1, h (e' p).2)` otherwise, where
`h = e'.coord_change_homeomorph e _ _` is the homeomorphism of the fiber such that
`h (e' p).2 = (e p).2` whenever `e p = a`. -/
/-
**Bundle.Trivialization.piecewiseLe** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializa
tion`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               [inst_3 : Linear
Order B] →                 [OrderTopology B] →                   (e e' : Bundle.
Trivialization F proj) →                     (a : B) → a ∈ e.baseSet → a ∈ e'.ba
seSet → Bundle.Trivialization F proj
参数：e e' : Bundle.Trivialization F proj；a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj :
 Z → B` over a
linearly ordered base `B` and a point `a ∈ e.baseSet ∩ e'.baseSet`, `e.piecewise
_le e' a He He'`
is the bundle trivialization over `Set.ite (Iic a) e.baseSet e'.baseSet` that is
 equal to `e` on
points `p` such that `proj p ≤ a` and is equal to `((e' p).1, h (e' p).2)` other
wise, where
`h = e'.coord_change_homeomorph e _ _` is the homeomorphism of the fiber such th
at
`h (e' p).2 = (e p).2` whenever `e p = a`.
-/
noncomputable def piecewiseLe [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) : Trivialization F proj :=
  e.piecewiseLeOfEq (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e He' He)) a He He' <| by
    rintro p rfl
    ext1
    · simp [*]
    · simp [*]

open scoped Classical in
/-- Given two bundle trivializations `e`, `e'` over disjoint sets, `e.disjoint_union e' H` is the
bundle trivialization over the union of the base sets that agrees with `e` and `e'` over their
base sets. -/
/-
**Bundle.Trivialization.disjointUnion** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Triviali
zation`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               (e e' : Bundle.T
rivialization F proj) → Disjoint e.baseSet e'.baseSet → Bundle.Trivialization F 
proj
参数：e e' : Bundle.Trivialization F proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two bundle trivializations `e`, `e'` over disjoint sets, `e.disjoint_union
 e' H` is the
bundle trivialization over the union of the base sets that agrees with `e` and `
e'` over their
base sets.
-/
noncomputable def disjointUnion (e e' : Trivialization F proj) (H : Disjoint e.baseSet e'.baseSet) :
    Trivialization F proj where
  toOpenPartialHomeomorph :=
    e.toOpenPartialHomeomorph.disjointUnion e'.toOpenPartialHomeomorph
      (by
        rw [e.source_eq, e'.source_eq]
        exact H.preimage _)
      (by
        rw [e.target_eq, e'.target_eq, disjoint_iff_inf_le]
        intro x hx
        exact H.le_bot ⟨hx.1.1, hx.2.1⟩)
  baseSet := e.baseSet ∪ e'.baseSet
  open_baseSet := IsOpen.union e.open_baseSet e'.open_baseSet
  source_eq := congr_arg₂ (· ∪ ·) e.source_eq e'.source_eq
  target_eq := (congr_arg₂ (· ∪ ·) e.target_eq e'.target_eq).trans union_prod.symm
  proj_toFun := by
    rintro p (hp | hp')
    · change (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_mem, e.coe_fst] <;> exact hp
    · change (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_notMem, e'.coe_fst hp']
      simp only [source_eq] at hp' ⊢
      exact fun h => H.le_bot ⟨h, hp'⟩

end Piecewise

section Lift

/-- The local lifting through a Trivialization `T` from the base to the leaf containing `z`. -/
/-
**Bundle.Trivialization.lift** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} → [inst_2 : TopologicalSpace Z] → Bundle.Trivialization F proj → Z → B → Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The local lifting through a Trivialization `T` from the base to the leaf contain
ing `z`.
-/
def lift (T : Trivialization F proj) (z : Z) (b : B) : Z := T.invFun (b, (T z).2)

variable {T : Trivialization F proj} {z : Z} {b : B}

@[simp]
/-
**Bundle.Trivialization.lift_self** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializati
on`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] {T
 : Bundle.Trivialization F proj} {z : Z}, proj z ∈ T.baseSet → T.lift z (proj z)
 = z
参数：proj z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.symm_apply_mk_proj`：∀ {B : Type u_1} {F : Type u_2
} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj
 : Z → B}   [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem lift_self (he : proj z ∈ T.baseSet) : T.lift z (proj z) = z :=
  symm_apply_mk_proj _ <| T.mem_source.2 he
/-
**Bundle.Trivialization.proj_lift** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializati
on`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] {T
 : Bundle.Trivialization F proj} {z : Z} {b : B},   b ∈ T.baseSet → proj (T.lift
 z b) = b
参数：T.lift z b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.proj_symm_apply`：∀ {B : Type u_1} {F : Type u_2} {
Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : 
Z → B}   [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_target`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
-/
theorem proj_lift (hx : b ∈ T.baseSet) : proj (T.lift z b) = b :=
  T.proj_symm_apply <| T.mem_target.2 hx

/-- The restriction of `lift` to the source and base set of `T`, as a bundled continuous map. -/
/-
**Bundle.Trivialization.liftCM** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`
。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] → (T : Bundle.Trivialization F p
roj) → C(↑T.source × ↑T.baseSet, ↑T.source)
参数：T : Bundle.Trivialization F proj；↑T.source × ↑T.baseSet, ↑T.source。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of `lift` to the source and base set of `T`, as a bundled contin
uous map.
-/
def liftCM (T : Trivialization F proj) : C(T.source × T.baseSet, T.source) where
  toFun ex := ⟨T.lift ex.1 ex.2, T.map_target (by simp [mem_target])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine T.continuousOn_invFun.comp_continuous ?_ (by simp [mem_target])
    refine .prodMk (by fun_prop) (.snd ?_)
    exact T.continuousOn_toFun.comp_continuous (by fun_prop) (by simp)

variable {ι : Type*} [TopologicalSpace ι] [LocallyCompactPair ι T.baseSet]
  {γ : C(ι, T.baseSet)} {i : ι} {e : T.source}

/-- Extension of `liftCM` to continuous maps taking values in `T.baseSet` (local version of
homotopy lifting) -/
/-
**Bundle.Trivialization.clift** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`。
形式化陈述：{B : Type u_1} →   {F : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace B] →         [inst_1 : TopologicalSpace F] →           {proj : Z →
 B} →             [inst_2 : TopologicalSpace Z] →               {ι : Type u_5} →
                 [inst_3 : TopologicalSpace ι] →                   (T : Bundle.T
rivialization F proj) →                     [LocallyCompactPair ι ↑T.baseSet] → 
C(↑T.source × C(ι, ↑T.baseSet), C(ι, ↑T.source))
参数：T : Bundle.Trivialization F proj；↑T.source × C(ι, ↑T.baseSet), C(ι, ↑T.source
)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension of `liftCM` to continuous maps taking values in `T.baseSet` (local ver
sion of
homotopy lifting)
-/
def clift (T : Trivialization F proj) [LocallyCompactPair ι T.baseSet] :
    C(T.source × C(ι, T.baseSet), C(ι, T.source)) := by
  let Ψ : C((T.source × C(ι, T.baseSet)) × ι, C(ι, T.baseSet) × ι) :=
    ⟨fun eγt => (eγt.1.2, eγt.2), by fun_prop⟩
  refine ContinuousMap.curry <| T.liftCM.comp <| ⟨fun eγt => ⟨eγt.1.1, eγt.1.2 eγt.2⟩, ?_⟩
  simpa using ⟨by fun_prop, ContinuousEval.continuous_eval.comp Ψ.continuous⟩

@[simp]
/-
**Bundle.Trivialization.clift_self** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializat
ion`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] {T
 : Bundle.Trivialization F proj} {ι : Type u_5} [inst_3 : TopologicalSpace ι]   
[inst_4 : LocallyCompactPair ι ↑T.baseSet] {γ : C(ι, ↑T.baseSet)} {i : ι} {e : ↑
T.source},   proj ↑e = ↑(γ i) → (T.clift (e, γ)) i = e
参数：ι, ↑T.baseSet；γ i；T.clift (e, γ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.lift_self`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}
   [inst_2 : Topologi…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem clift_self (h : proj e.1 = γ i) :
    T.clift (e, γ) i = e := by
  have : proj e ∈ T.baseSet := by simp [h]
  simp [clift, liftCM, ← h, lift_self, this]
/-
**Bundle.Trivialization.proj_clift** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializat
ion`。
形式化陈述：∀ {B : Type u_1} {F : Type u_2} {Z : Type u_4} [inst : TopologicalSpace B]
 [inst_1 : TopologicalSpace F] {proj : Z → B}   [inst_2 : TopologicalSpace Z] {T
 : Bundle.Trivialization F proj} {ι : Type u_5} [inst_3 : TopologicalSpace ι]   
[inst_4 : LocallyCompactPair ι ↑T.baseSet] {γ : C(ι, ↑T.baseSet)} {i : ι} {e : ↑
T.source},   proj ↑((T.clift (e, γ)) i) = ↑(γ i)
参数：ι, ↑T.baseSet；(T.clift (e, γ)) i；γ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.proj_lift`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}
   [inst_2 : Topologi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem proj_clift : proj (T.clift (e, γ) i) = γ i := by
  simp [clift, liftCM, proj_lift]

end Lift

end Bundle.Trivialization

