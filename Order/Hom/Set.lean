/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.MinImports

/-!
# Order homomorphisms and sets
-/

@[expose] public section


open OrderDual Set

variable {α β γ : Type*}

namespace Set

set_option backward.isDefEq.respectTransparency false in
/-- Sets on sum types are order-equivalent to pairs of sets on each summand. -/
@[simps apply]
/--
Definition of `sumEquiv` / `sumEquiv` 的定义

English:
definition sumEquiv
  signature: : Set (α oplus β) ≃o Set α × Set β where
  body: (Sum.inl ⁻¹' s, Sum.inr ⁻¹' s)
  invFun s := Sum.inl '' s.1 union Sum.inr '' s.2
  left_inv s := image_preimage_inl_union_image_preimage_inr s
  right_inv s := by
    simp [preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective]
  map_rel_iff' := by simp [subset_def]

@[simp]

中文:
定义 sumEquiv
  签名: : 集合 (α oplus β) ≃o 集合 α × 集合 β where
  定义体: (Sum.inl ⁻¹' s, Sum.inr ⁻¹' s)
  invFun s := Sum.inl '' s.1 union Sum.inr '' s.2
  left_inv s := image_preimage_inl_union_image_preimage_inr s
  right_inv s := by
    simp [preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective]
  map_rel_iff' := by simp [subset_def]

@[simp]

Depends on / 依赖: Sum.inl, Sum.inr
-/
def sumEquiv : Set (α oplus β) ≃o Set α × Set β where
  toFun s := (Sum.inl ⁻¹' s, Sum.inr ⁻¹' s)
  invFun s := Sum.inl '' s.1 union Sum.inr '' s.2
  left_inv s := image_preimage_inl_union_image_preimage_inr s
  right_inv s := by
    simp [preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective]
  map_rel_iff' := by simp [subset_def]

@[simp]
/--
theorem `sumEquiv_symm_apply` / 定理 `sumEquiv_symm_apply`

English:
theorem sumEquiv_symm_apply
  given: {s : Set α × Set β}
  proof: rfl

中文:
定理 sumEquiv_symm_apply
  条件: {s : 集合 α × 集合 β}
  证明: rfl
-/
theorem sumEquiv_symm_apply {s : Set α × Set β} :
    sumEquiv.symm s = Sum.inl '' s.1 union Sum.inr '' s.2 := rfl

/--
theorem `MapsTo.sumElim` / 定理 `MapsTo.sumElim`

English:
theorem MapsTo.sumElim
  statement: {f : α -> γ} {g : β -> γ} {s : Set α × Set β} {t : Set γ}
  proof: by
  rintro (a | b) <;> aesop

中文:
定理 映射到.sumElim
  结论: {f : α -> γ} {g : β -> γ} {s : 集合 α × 集合 β} {t : 集合 γ}
  证明: by
  rintro (a | b) <;> aesop
-/
theorem MapsTo.sumElim {f : α -> γ} {g : β -> γ} {s : Set α × Set β} {t : Set γ}
    (hf : Set.MapsTo f s.1 t) (hg : Set.MapsTo g s.2 t) :
    Set.MapsTo (Sum.elim f g) (Set.sumEquiv.symm s) t := by
  rintro (a | b) <;> aesop

/--
theorem `InjOn.sumElim` / 定理 `InjOn.sumElim`

English:
theorem InjOn.sumElim
  statement: {f : α -> γ} {g : β -> γ} {s : Set α × Set β}
  proof: by
  rintro (a₁ | b₁) h₁ (a₂ | b₂) h₂ heq <;> aesop

中文:
定理 单射限制.sumElim
  结论: {f : α -> γ} {g : β -> γ} {s : 集合 α × 集合 β}
  证明: by
  rintro (a₁ | b₁) h₁ (a₂ | b₂) h₂ heq <;> aesop
-/
theorem InjOn.sumElim {f : α -> γ} {g : β -> γ} {s : Set α × Set β}
    (hf : Set.InjOn f s.1) (hg : Set.InjOn g s.2) (hfg : forallᵉ (a in s.1) (b in s.2), f a != g b) :
    Set.InjOn (Sum.elim f g) (Set.sumEquiv.symm s) := by
  rintro (a₁ | b₁) h₁ (a₂ | b₂) h₂ heq <;> aesop

end Set

namespace OrderIso

section LE

variable [LE α] [LE β]

/--
theorem `range_eq` / 定理 `range_eq`

English:
theorem range_eq
  given: (e : α ≃o β)
  statement: Set.range e = Set.univ
  proof: e.surjective.range_eq

@[simp]

中文:
定理 range_eq
  条件: (e : α ≃o β)
  结论: 集合.range e = 集合.univ
  证明: e.surjective.range_eq

@[simp]

Depends on / 依赖: e.surjective.range_eq, range_eq, surjective
-/
theorem range_eq (e : α ≃o β) : Set.range e = Set.univ :=
  e.surjective.range_eq

@[simp]
/--
theorem `symm_image_image` / 定理 `symm_image_image`

English:
theorem symm_image_image
  given: (e : α ≃o β) (s : Set α)
  statement: e.symm '' e '' s = s
  proof: e.toEquiv.symm_image_image s

@[simp]

中文:
定理 symm_image_image
  条件: (e : α ≃o β) (s : 集合 α)
  结论: e.symm '' e '' s = s
  证明: e.toEquiv.symm_image_image s

@[simp]

Depends on / 依赖: e.toEquiv.symm_image_image, symm_image_image, toEquiv
-/
theorem symm_image_image (e : α ≃o β) (s : Set α) : e.symm '' e '' s = s :=
  e.toEquiv.symm_image_image s

@[simp]
/--
theorem `image_symm_image` / 定理 `image_symm_image`

English:
theorem image_symm_image
  given: (e : α ≃o β) (s : Set β)
  statement: e '' e.symm '' s = s
  proof: e.toEquiv.image_symm_image s

中文:
定理 image_symm_image
  条件: (e : α ≃o β) (s : 集合 β)
  结论: e '' e.symm '' s = s
  证明: e.toEquiv.image_symm_image s

Depends on / 依赖: e.toEquiv.image_symm_image, image_symm_image, toEquiv
-/
theorem image_symm_image (e : α ≃o β) (s : Set β) : e '' e.symm '' s = s :=
  e.toEquiv.image_symm_image s

/--
theorem `image_eq_preimage_symm` / 定理 `image_eq_preimage_symm`

English:
theorem image_eq_preimage_symm
  given: (e : α ≃o β) (s : Set α)
  statement: e '' s = e.symm ⁻¹' s
  proof: e.toEquiv.image_eq_preimage_symm s

@[simp]

中文:
定理 image_eq_preimage_symm
  条件: (e : α ≃o β) (s : 集合 α)
  结论: e '' s = e.symm ⁻¹' s
  证明: e.toEquiv.image_eq_preimage_symm s

@[simp]

Depends on / 依赖: e.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem image_eq_preimage_symm (e : α ≃o β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s

@[simp]
/--
theorem `preimage_symm_preimage` / 定理 `preimage_symm_preimage`

English:
theorem preimage_symm_preimage
  given: (e : α ≃o β) (s : Set α)
  statement: e ⁻¹' e.symm ⁻¹' s = s
  proof: e.toEquiv.preimage_symm_preimage s

@[simp]

中文:
定理 preimage_symm_preimage
  条件: (e : α ≃o β) (s : 集合 α)
  结论: e ⁻¹' e.symm ⁻¹' s = s
  证明: e.toEquiv.preimage_symm_preimage s

@[simp]

Depends on / 依赖: e.toEquiv.preimage_symm_preimage, preimage_symm_preimage, toEquiv
-/
theorem preimage_symm_preimage (e : α ≃o β) (s : Set α) : e ⁻¹' e.symm ⁻¹' s = s :=
  e.toEquiv.preimage_symm_preimage s

@[simp]
/--
theorem `symm_preimage_preimage` / 定理 `symm_preimage_preimage`

English:
theorem symm_preimage_preimage
  given: (e : α ≃o β) (s : Set β)
  statement: e.symm ⁻¹' e ⁻¹' s = s
  proof: e.toEquiv.symm_preimage_preimage s

@[simp]

中文:
定理 symm_preimage_preimage
  条件: (e : α ≃o β) (s : 集合 β)
  结论: e.symm ⁻¹' e ⁻¹' s = s
  证明: e.toEquiv.symm_preimage_preimage s

@[simp]

Depends on / 依赖: e.toEquiv.symm_preimage_preimage, symm_preimage_preimage, toEquiv
-/
theorem symm_preimage_preimage (e : α ≃o β) (s : Set β) : e.symm ⁻¹' e ⁻¹' s = s :=
  e.toEquiv.symm_preimage_preimage s

@[simp]
/--
theorem `image_preimage` / 定理 `image_preimage`

English:
theorem image_preimage
  given: (e : α ≃o β) (s : Set β)
  statement: e '' e ⁻¹' s = s
  proof: e.toEquiv.image_preimage s

@[simp]

中文:
定理 image_preimage
  条件: (e : α ≃o β) (s : 集合 β)
  结论: e '' e ⁻¹' s = s
  证明: e.toEquiv.image_preimage s

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, e.toEquiv.image_preimage, image_preimage, of_algebraMap_eq, toEquiv
-/
theorem image_preimage (e : α ≃o β) (s : Set β) : e '' e ⁻¹' s = s :=
  e.toEquiv.image_preimage s

@[simp]
/--
theorem `preimage_image` / 定理 `preimage_image`

English:
theorem preimage_image
  given: (e : α ≃o β) (s : Set α)
  statement: e ⁻¹' e '' s = s
  proof: e.toEquiv.preimage_image s

中文:
定理 preimage_image
  条件: (e : α ≃o β) (s : 集合 α)
  结论: e ⁻¹' e '' s = s
  证明: e.toEquiv.preimage_image s

Depends on / 依赖: e.toEquiv.preimage_image, preimage_image, toEquiv
-/
theorem preimage_image (e : α ≃o β) (s : Set α) : e ⁻¹' e '' s = s :=
  e.toEquiv.preimage_image s

end LE

open Set

variable [Preorder α]

/-- Order isomorphism between two equal sets. -/
@[simps! apply symm_apply]
/--
Definition of `setCongr` / `setCongr` 的定义

English:
definition setCongr
  signature: (s t : Set α) (h : s = t)
  body: Equiv.setCongr h
  map_rel_iff' := Iff.rfl

中文:
定义 setCongr
  签名: (s t : 集合 α) (h : s = t)
  定义体: Equiv.setCongr h
  map_rel_iff' := Iff.rfl

Depends on / 依赖: Equiv.setCongr, setCongr
-/
def setCongr (s t : Set α) (h : s = t) :
    s ≃o t where
  toEquiv := Equiv.setCongr h
  map_rel_iff' := Iff.rfl

/--
Definition of `Set.univ` / `Set.univ` 的定义

English:
definition Set.univ
  signature: : (Set.univ : Set α) ≃o α where
  body: Equiv.Set.univ α
  map_rel_iff' := Iff.rfl

中文:
定义 集合.univ
  签名: : (集合.univ : 集合 α) ≃o α where
  定义体: Equiv.Set.univ α
  map_rel_iff' := Iff.rfl
-/
def Set.univ : (Set.univ : Set α) ≃o α where
  toEquiv := Equiv.Set.univ α
  map_rel_iff' := Iff.rfl

end OrderIso

/-- We can regard an order embedding as an order isomorphism to its range. -/
@[simps! apply]
/--
Definition of `OrderEmbedding.orderIso` / `OrderEmbedding.orderIso` 的定义

English:
definition OrderEmbedding.orderIso
  signature: [LE α] [LE β] {f : α ↪o β}
  body: { Equiv.ofInjective _ f.injective with
    map_rel_iff' := f.map_rel_iff }

中文:
定义 OrderEmbedding.orderIso
  签名: [LE α] [LE β] {f : α ↪o β}
  定义体: { Equiv.ofInjective _ f.injective with
    map_rel_iff' := f.map_rel_iff }

Depends on / 依赖: Equiv.ofInjective, f.injective, f.map_rel_iff, injective, map_rel_iff, ofInjective
-/
noncomputable def OrderEmbedding.orderIso [LE α] [LE β] {f : α ↪o β} :
    α ≃o Set.range f :=
  { Equiv.ofInjective _ f.injective with
    map_rel_iff' := f.map_rel_iff }

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def StrictMonoOn.orderIso {α β} [LinearOrder α] [Preorder β] (f : α -> β)
  body: hf.injOn.bijOn_image.equiv _
  map_rel_iff' := hf.le_iff_le (Subtype.property _) (Subtype.property _)

中文:
定义 noncomputable
  签名: def StrictMonoOn.orderIso {α β} [线性序 α] [预序 β] (f : α -> β)
  定义体: hf.injOn.bijOn_image.equiv _
  map_rel_iff' := hf.le_iff_le (Subtype.property _) (Subtype.property _)
-/
protected noncomputable def StrictMonoOn.orderIso {α β} [LinearOrder α] [Preorder β] (f : α -> β)
    (s : Set α) (hf : StrictMonoOn f s) :
    s ≃o f '' s where
  toEquiv := hf.injOn.bijOn_image.equiv _
  map_rel_iff' := hf.le_iff_le (Subtype.property _) (Subtype.property _)

namespace StrictMono

variable [LinearOrder α] [Preorder β]
variable (f : α -> β) (h_mono : StrictMono f) (h_surj : Function.Surjective f)

/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
@[simps! apply]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def orderIso
  body: Equiv.ofInjective f h_mono.injective
  map_rel_iff' := h_mono.le_iff_le

中文:
定义 noncomputable
  签名: def orderIso
  定义体: Equiv.ofInjective f h_mono.injective
  map_rel_iff' := h_mono.le_iff_le
-/
protected noncomputable def orderIso :
    α ≃o Set.range f where
  toEquiv := Equiv.ofInjective f h_mono.injective
  map_rel_iff' := h_mono.le_iff_le

/--
Definition of `orderIsoOfSurjective` / `orderIsoOfSurjective` 的定义

English:
definition orderIsoOfSurjective
  signature: : α ≃o β
  body: (h_mono.orderIso f).trans
    (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ

@[simp]

中文:
定义 orderIsoOfSurjective
  签名: : α ≃o β
  定义体: (h_mono.orderIso f).trans
    (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ

@[simp]

Depends on / 依赖: OrderIso, OrderIso.Set.univ, OrderIso.setCongr, h_mono, h_mono.orderIso, h_surj, h_surj.range_eq, orderIso, range_eq, setCongr
-/
noncomputable def orderIsoOfSurjective : α ≃o β :=
(h_mono.orderIso f).trans
    (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ

@[simp]
/--
theorem `coe_orderIsoOfSurjective` / 定理 `coe_orderIsoOfSurjective`

English:
theorem coe_orderIsoOfSurjective
  statement: (orderIsoOfSurjective f h_mono h_surj : α -> β) = f
  proof: rfl

@[simp]

中文:
定理 coe_orderIsoOfSurjective
  结论: (orderIsoOfSurjective f h_mono h_surj : α -> β) = f
  证明: rfl

@[simp]
-/
theorem coe_orderIsoOfSurjective : (orderIsoOfSurjective f h_mono h_surj : α -> β) = f :=
  rfl

@[simp]
/--
theorem `orderIsoOfSurjective_symm_apply_self` / 定理 `orderIsoOfSurjective_symm_apply_self`

English:
theorem orderIsoOfSurjective_symm_apply_self
  given: (a : α)
  proof: (orderIsoOfSurjective f h_mono h_surj).symm_apply_apply _

中文:
定理 orderIsoOfSurjective_symm_apply_self
  条件: (a : α)
  证明: (orderIsoOfSurjective f h_mono h_surj).symm_apply_apply _

Depends on / 依赖: h_mono, h_surj, orderIsoOfSurjective, symm_apply_apply
-/
theorem orderIsoOfSurjective_symm_apply_self (a : α) :
    (orderIsoOfSurjective f h_mono h_surj).symm (f a) = a :=
  (orderIsoOfSurjective f h_mono h_surj).symm_apply_apply _

/--
theorem `orderIsoOfSurjective_self_symm_apply` / 定理 `orderIsoOfSurjective_self_symm_apply`

English:
theorem orderIsoOfSurjective_self_symm_apply
  given: (b : β)
  proof: (orderIsoOfSurjective f h_mono h_surj).apply_symm_apply _

中文:
定理 orderIsoOfSurjective_self_symm_apply
  条件: (b : β)
  证明: (orderIsoOfSurjective f h_mono h_surj).apply_symm_apply _

Depends on / 依赖: apply_symm_apply, h_mono, h_surj, orderIsoOfSurjective
-/
theorem orderIsoOfSurjective_self_symm_apply (b : β) :
    f ((orderIsoOfSurjective f h_mono h_surj).symm b) = b :=
  (orderIsoOfSurjective f h_mono h_surj).apply_symm_apply _

end StrictMono

/--
lemma `OrderEmbedding.range_inj` / 引理 `OrderEmbedding.range_inj`

English:
lemma OrderEmbedding.range_inj
  given: [LinearOrder α] [WellFoundedLT α] [Preorder β] {f g : α ↪o β}
  proof: by
  rw [f.strictMono.range_inj g.strictMono]; rw [DFunLike.coe_fn_eq]

中文:
引理 OrderEmbedding.range_inj
  条件: [线性序 α] [WellFoundedLT α] [预序 β] {f g : α ↪o β}
  证明: by
  rw [f.strictMono.range_inj g.strictMono]; rw [DFunLike.coe_fn_eq]

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, coe_fn_eq, f.strictMono.range_inj, g.strictMono, range_inj, strictMono
-/
lemma OrderEmbedding.range_inj [LinearOrder α] [WellFoundedLT α] [Preorder β] {f g : α ↪o β} :
    Set.range f = Set.range g ↔ f = g := by
  rw [f.strictMono.range_inj g.strictMono]; rw [DFunLike.coe_fn_eq]

namespace OrderIso

-- These results are also true whenever β is well-founded instead of α.
-- You can use `RelEmbedding.isWellFounded` to transfer the instance over.

/--
Instance `subsingleton_of_wellFoundedLT` / 实例 `subsingleton_of_wellFoundedLT`

English:
instance subsingleton_of_wellFoundedLT
  signature: [LinearOrder α] [WellFoundedLT α] [Preorder β]
  body: by
  refine ⟨fun f g => ?_⟩
  rw [OrderIso.ext_iff]; rw [← coe_toOrderEmbedding]; rw [← coe_toOrderEmbedding]; rw [DFunLike.coe_fn_eq]; rw [← OrderEmbedding.range_inj]; rw [coe_toOrderEmbedding]; rw [coe_toOrderEmbedding]; rw [range_eq]; rw [range_eq]

中文:
实例 subsingleton_of_wellFoundedLT
  签名: [线性序 α] [WellFoundedLT α] [预序 β]
  定义体: by
  refine ⟨fun f g => ?_⟩
  rw [OrderIso.ext_iff]; rw [← coe_toOrderEmbedding]; rw [← coe_toOrderEmbedding]; rw [DFunLike.coe_fn_eq]; rw [← OrderEmbedding.range_inj]; rw [coe_toOrderEmbedding]; rw [coe_toOrderEmbedding]; rw [range_eq]; rw [range_eq]

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, OrderEmbedding, OrderEmbedding.range_inj, OrderIso, OrderIso.ext_iff, coe_fn_eq, coe_toOrderEmbedding, ext_iff, range_eq, range_inj
-/
instance subsingleton_of_wellFoundedLT [LinearOrder α] [WellFoundedLT α] [Preorder β] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g => ?_⟩
  rw [OrderIso.ext_iff]; rw [← coe_toOrderEmbedding]; rw [← coe_toOrderEmbedding]; rw [DFunLike.coe_fn_eq]; rw [← OrderEmbedding.range_inj]; rw [coe_toOrderEmbedding]; rw [coe_toOrderEmbedding]; rw [range_eq]; rw [range_eq]

/--
Instance `subsingleton_of_wellFoundedLT'` / 实例 `subsingleton_of_wellFoundedLT'`

English:
instance subsingleton_of_wellFoundedLT'
  signature: [LinearOrder β] [WellFoundedLT β] [Preorder α]
  body: by
  refine ⟨fun f g => ?_⟩
  change f.symm.symm = g.symm.symm
  rw [Subsingleton.elim f.symm]

中文:
实例 subsingleton_of_wellFoundedLT'
  签名: [线性序 β] [WellFoundedLT β] [预序 α]
  定义体: by
  refine ⟨fun f g => ?_⟩
  change f.symm.symm = g.symm.symm
  rw [Subsingleton.elim f.symm]

Depends on / 依赖: Subsingleton, Subsingleton.elim, f.symm, f.symm.symm, g.symm.symm
-/
instance subsingleton_of_wellFoundedLT' [LinearOrder β] [WellFoundedLT β] [Preorder α] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g => ?_⟩
  change f.symm.symm = g.symm.symm
  rw [Subsingleton.elim f.symm]

/--
Instance `unique_of_wellFoundedLT` / 实例 `unique_of_wellFoundedLT`

English:
instance unique_of_wellFoundedLT
  signature: [LinearOrder α] [WellFoundedLT α]
  body: Unique.mk' _

中文:
实例 unique_of_wellFoundedLT
  签名: [线性序 α] [WellFoundedLT α]
  定义体: Unique.mk' _

Depends on / 依赖: Unique, Unique.mk
-/
instance unique_of_wellFoundedLT [LinearOrder α] [WellFoundedLT α] : Unique (α ≃o α) := Unique.mk' _

/--
Instance `subsingleton_of_wellFoundedGT` / 实例 `subsingleton_of_wellFoundedGT`

English:
instance subsingleton_of_wellFoundedGT
  signature: [LinearOrder α] [WellFoundedGT α] [Preorder β]
  body: by
  refine ⟨fun f g => ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]

中文:
实例 subsingleton_of_wellFoundedGT
  签名: [线性序 α] [WellFoundedGT α] [预序 β]
  定义体: by
  refine ⟨fun f g => ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]

Depends on / 依赖: Subsingleton, Subsingleton.elim, f.dual, f.dual.dual, g.dual.dual
-/
instance subsingleton_of_wellFoundedGT [LinearOrder α] [WellFoundedGT α] [Preorder β] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g => ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]

/--
Instance `subsingleton_of_wellFoundedGT'` / 实例 `subsingleton_of_wellFoundedGT'`

English:
instance subsingleton_of_wellFoundedGT'
  signature: [LinearOrder β] [WellFoundedGT β] [Preorder α]
  body: by
  refine ⟨fun f g => ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]

中文:
实例 subsingleton_of_wellFoundedGT'
  签名: [线性序 β] [WellFoundedGT β] [预序 α]
  定义体: by
  refine ⟨fun f g => ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]

Depends on / 依赖: Subsingleton, Subsingleton.elim, f.dual, f.dual.dual, g.dual.dual
-/
instance subsingleton_of_wellFoundedGT' [LinearOrder β] [WellFoundedGT β] [Preorder α] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g => ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]

/--
Instance `unique_of_wellFoundedGT` / 实例 `unique_of_wellFoundedGT`

English:
instance unique_of_wellFoundedGT
  signature: [LinearOrder α] [WellFoundedGT α]
  body: Unique.mk' _

中文:
实例 unique_of_wellFoundedGT
  签名: [线性序 α] [WellFoundedGT α]
  定义体: Unique.mk' _

Depends on / 依赖: Unique, Unique.mk
-/
instance unique_of_wellFoundedGT [LinearOrder α] [WellFoundedGT α] : Unique (α ≃o α) := Unique.mk' _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Iic` / `Iic` 的定义

English:
definition Iic
  signature: [Lattice α] [Lattice β] (e : α ≃o β) (x : α)
  body: ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.symm_apply_le.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

中文:
定义 左无界右闭区间
  签名: [格 α] [格 β] (e : α ≃o β) (x : α)
  定义体: ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.symm_apply_le.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp
-/
protected def Iic [Lattice α] [Lattice β] (e : α ≃o β) (x : α) :
    Iic x ≃o Iic (e x) where
  toFun y := ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.symm_apply_le.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Ici` / `Ici` 的定义

English:
definition Ici
  signature: [Lattice α] [Lattice β] (e : α ≃o β) (x : α)
  body: ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.le_symm_apply.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

中文:
定义 左闭右无界区间
  签名: [格 α] [格 β] (e : α ≃o β) (x : α)
  定义体: ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.le_symm_apply.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp
-/
protected def Ici [Lattice α] [Lattice β] (e : α ≃o β) (x : α) :
    Ici x ≃o Ici (e x) where
  toFun y := ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.le_symm_apply.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Icc` / `Icc` 的定义

English:
definition Icc
  signature: [Lattice α] [Lattice β] (e : α ≃o β) (x y : α)
  body: ⟨e z, by simp only [mem_Icc, map_le_map_iff]; exact z.property⟩
  invFun z := ⟨e.symm z, by simp only [mem_Icc, e.le_symm_apply, e.symm_apply_le]; exact z.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

中文:
定义 闭区间
  签名: [格 α] [格 β] (e : α ≃o β) (x y : α)
  定义体: ⟨e z, by simp only [mem_Icc, map_le_map_iff]; exact z.property⟩
  invFun z := ⟨e.symm z, by simp only [mem_Icc, e.le_symm_apply, e.symm_apply_le]; exact z.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp
-/
protected def Icc [Lattice α] [Lattice β] (e : α ≃o β) (x y : α) :
    Icc x y ≃o Icc (e x) (e y) where
  toFun z := ⟨e z, by simp only [mem_Icc, map_le_map_iff]; exact z.property⟩
  invFun z := ⟨e.symm z, by simp only [mem_Icc, e.le_symm_apply, e.symm_apply_le]; exact z.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

end OrderIso

section BooleanAlgebra

variable (α) [BooleanAlgebra α]

/-- Taking complements as an order isomorphism to the order dual. -/
@[simps!]
/--
Definition of `OrderIso.compl` / `OrderIso.compl` 的定义

English:
definition OrderIso.compl
  signature: : α ≃o αᵒᵈ where
  body: OrderDual.toDual ∘ Compl.compl
  invFun := Compl.compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl (α := αᵒᵈ)
  map_rel_iff' := compl_le_compl_iff_le

中文:
定义 OrderIso.compl
  签名: : α ≃o αᵒᵈ where
  定义体: OrderDual.toDual ∘ Compl.compl
  invFun := Compl.compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl (α := αᵒᵈ)
  map_rel_iff' := compl_le_compl_iff_le

Depends on / 依赖: Compl.compl, OrderDual, OrderDual.toDual, toDual
-/
def OrderIso.compl : α ≃o αᵒᵈ where
  toFun := OrderDual.toDual ∘ Compl.compl
  invFun := Compl.compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl (α := αᵒᵈ)
  map_rel_iff' := compl_le_compl_iff_le

/--
theorem `compl_strictAnti` / 定理 `compl_strictAnti`

English:
theorem compl_strictAnti
  statement: StrictAnti (compl : α -> α)
  proof: (OrderIso.compl α).strictMono

中文:
定理 compl_strictAnti
  结论: 严格递减 (compl : α -> α)
  证明: (OrderIso.compl α).strictMono

Depends on / 依赖: OrderIso, OrderIso.compl, strictMono
-/
theorem compl_strictAnti : StrictAnti (compl : α -> α) :=
  (OrderIso.compl α).strictMono

/--
theorem `compl_antitone` / 定理 `compl_antitone`

English:
theorem compl_antitone
  statement: Antitone (compl : α -> α)
  proof: (OrderIso.compl α).monotone

中文:
定理 compl_antitone
  结论: 递减 (compl : α -> α)
  证明: (OrderIso.compl α).monotone

Depends on / 依赖: OrderIso, OrderIso.compl, monotone
-/
theorem compl_antitone : Antitone (compl : α -> α) :=
  (OrderIso.compl α).monotone

end BooleanAlgebra
