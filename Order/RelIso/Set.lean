/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Order.Directed
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Logic.Embedding.Set
public import Mathlib.Logic.Equiv.Set

/-!
# Interactions between relation homomorphisms and sets

It is likely that there are better homes for many of these statement,
in files further down the import graph.
-/

@[expose] public section


open Function

universe u v w

variable {α β : Type*} {r : α -> α -> Prop} {s : β -> β -> Prop}

namespace RelHomClass

variable {F : Type*}

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  statement: [SemilatticeInf α] [LinearOrder β] [FunLike F β α]
  proof: (StrictMono.monotone fun _ _ => map_rel a).map_inf m n

中文:
定理 map_inf
  结论: [SemilatticeInf α] [线性序 β] [函数状 F β α]
  证明: (StrictMono.monotone fun _ _ => map_rel a).map_inf m n

Depends on / 依赖: StrictMono, StrictMono.monotone, map_inf, map_rel, monotone
-/
theorem map_inf [SemilatticeInf α] [LinearOrder β] [FunLike F β α]
    [RelHomClass F (· < ·) (· < ·)] (a : F) (m n : β) :
    a (m ⊓ n) = a m ⊓ a n :=
  (StrictMono.monotone fun _ _ => map_rel a).map_inf m n

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  statement: [SemilatticeSup α] [LinearOrder β] [FunLike F β α]
  proof: map_inf (α := αᵒᵈ) (β := βᵒᵈ) _ _ _

中文:
定理 map_sup
  结论: [SemilatticeSup α] [线性序 β] [函数状 F β α]
  证明: map_inf (α := αᵒᵈ) (β := βᵒᵈ) _ _ _

Depends on / 依赖: map_inf
-/
theorem map_sup [SemilatticeSup α] [LinearOrder β] [FunLike F β α]
    [RelHomClass F (· > ·) (· > ·)] (a : F) (m n : β) :
    a (m ⊔ n) = a m ⊔ a n :=
  map_inf (α := αᵒᵈ) (β := βᵒᵈ) _ _ _

/--
theorem `directed` / 定理 `directed`

English:
theorem directed
  statement: [FunLike F α β] [RelHomClass F r s] {ι : Sort*} {a : ι -> α} {f : F}
  proof: ha.mono_comp _ fun _ _ h => map_rel f h

中文:
定理 directed
  结论: [函数状 F α β] [关系态射类 F r s] {ι : 类型层*} {a : ι -> α} {f : F}
  证明: ha.mono_comp _ fun _ _ h => map_rel f h

Depends on / 依赖: ha.mono_comp, map_rel, mono_comp
-/
theorem directed [FunLike F α β] [RelHomClass F r s] {ι : Sort*} {a : ι -> α} {f : F}
    (ha : Directed r a) : Directed s (f ∘ a) :=
  ha.mono_comp _ fun _ _ h => map_rel f h

/--
theorem `directedOn` / 定理 `directedOn`

English:
theorem directedOn
  statement: [FunLike F α β] [RelHomClass F r s] {f : F}
  proof: hs.mono_comp fun _ _ h => map_rel f h

中文:
定理 directedOn
  结论: [函数状 F α β] [关系态射类 F r s] {f : F}
  证明: hs.mono_comp fun _ _ h => map_rel f h

Depends on / 依赖: hs.mono_comp, map_rel, mono_comp
-/
theorem directedOn [FunLike F α β] [RelHomClass F r s] {f : F}
    {t : Set α} (hs : DirectedOn r t) : DirectedOn s (f '' t) :=
  hs.mono_comp fun _ _ h => map_rel f h

end RelHomClass

namespace RelIso

/--
theorem `range_eq` / 定理 `range_eq`

English:
theorem range_eq
  given: (e : r ≃r s)
  statement: Set.range e = Set.univ
  proof: by simp

中文:
定理 range_eq
  条件: (e : r ≃r s)
  结论: 集合.range e = 集合.univ
  证明: by simp
-/
theorem range_eq (e : r ≃r s) : Set.range e = Set.univ := by simp

end RelIso

/--
Definition of `Subrel` / `Subrel` 的定义

English:
definition Subrel
  signature: (r : α -> α -> Prop) (p : α -> Prop)
  body: Subtype.val ⁻¹'o r

@[simp]

中文:
定义 Subrel
  签名: (r : α -> α -> 命题) (p : α -> 命题)
  定义体: Subtype.val ⁻¹'o r

@[simp]

Depends on / 依赖: Subtype, Subtype.val
-/
def Subrel (r : α -> α -> Prop) (p : α -> Prop) : Subtype p -> Subtype p -> Prop :=
  Subtype.val ⁻¹'o r

@[simp]
/--
theorem `subrel_val` / 定理 `subrel_val`

English:
theorem subrel_val
  given: (r : α -> α -> Prop) (p : α -> Prop) {a b}
  statement: Subrel r p a b ↔ r a.1 b.1
  proof: Iff.rfl

中文:
定理 subrel_val
  条件: (r : α -> α -> 命题) (p : α -> 命题) {a b}
  结论: Subrel r p a b ↔ r a.1 b.1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem subrel_val (r : α -> α -> Prop) (p : α -> Prop) {a b} : Subrel r p a b ↔ r a.1 b.1 :=
  Iff.rfl

namespace Subrel

/--
Definition of `relEmbedding` / `relEmbedding` 的定义

English:
definition relEmbedding
  signature: (r : α -> α -> Prop) (p : α -> Prop)
  body: ⟨Embedding.subtype _, Iff.rfl⟩

@[simp]

中文:
定义 relEmbedding
  签名: (r : α -> α -> 命题) (p : α -> 命题)
  定义体: ⟨Embedding.subtype _, Iff.rfl⟩

@[simp]
-/
protected def relEmbedding (r : α -> α -> Prop) (p : α -> Prop) : Subrel r p ↪r r :=
  ⟨Embedding.subtype _, Iff.rfl⟩

@[simp]
/--
theorem `relEmbedding_apply` / 定理 `relEmbedding_apply`

English:
theorem relEmbedding_apply
  given: (r : α -> α -> Prop) (p a)
  statement: Subrel.relEmbedding r p a = a.1
  proof: rfl

中文:
定理 relEmbedding_apply
  条件: (r : α -> α -> 命题) (p a)
  结论: Subrel.relEmbedding r p a = a.1
  证明: rfl
-/
theorem relEmbedding_apply (r : α -> α -> Prop) (p a) : Subrel.relEmbedding r p a = a.1 :=
  rfl

/--
Definition of `inclusionEmbedding` / `inclusionEmbedding` 的定义

English:
definition inclusionEmbedding
  signature: (r : α -> α -> Prop) {s t : Set α} (h : s subseteq t)
  body: Set.inclusion h
  inj' _ _ h := (Set.inclusion_inj _).mp h
  map_rel_iff' := Iff.rfl

@[simp]

中文:
定义 inclusionEmbedding
  签名: (r : α -> α -> 命题) {s t : 集合 α} (h : s subseteq t)
  定义体: Set.inclusion h
  inj' _ _ h := (Set.inclusion_inj _).mp h
  map_rel_iff' := Iff.rfl

@[simp]
-/
protected def inclusionEmbedding (r : α -> α -> Prop) {s t : Set α} (h : s subseteq t) :
    Subrel r (· in s) ↪r Subrel r (· in t) where
  toFun := Set.inclusion h
  inj' _ _ h := (Set.inclusion_inj _).mp h
  map_rel_iff' := Iff.rfl

@[simp]
/--
theorem `coe_inclusionEmbedding` / 定理 `coe_inclusionEmbedding`

English:
theorem coe_inclusionEmbedding
  given: (r : α -> α -> Prop) {s t : Set α} (h : s subseteq t)
  proof: rfl

中文:
定理 coe_inclusionEmbedding
  条件: (r : α -> α -> 命题) {s t : 集合 α} (h : s subseteq t)
  证明: rfl
-/
theorem coe_inclusionEmbedding (r : α -> α -> Prop) {s t : Set α} (h : s subseteq t) :
    (Subrel.inclusionEmbedding r h : s -> t) = Set.inclusion h :=
  rfl

instance (r : α -> α -> Prop) [Std.Refl r] (p : α -> Prop) : Std.Refl (Subrel r p) :=
  ⟨fun x => Std.Refl.refl (r := r) x⟩

instance (r : α -> α -> Prop) [Std.Symm r] (p : α -> Prop) : Std.Symm (Subrel r p) :=
  ⟨fun x y => Std.Symm.symm (r := r) x y⟩

instance (r : α -> α -> Prop) [Std.Asymm r] (p : α -> Prop) : Std.Asymm (Subrel r p) :=
  ⟨fun x y => Std.Asymm.asymm (r := r) x y⟩

instance (r : α -> α -> Prop) [IsTrans α r] (p : α -> Prop) : IsTrans _ (Subrel r p) :=
  ⟨fun x y z => IsTrans.trans (r := r) x y z⟩

instance (r : α -> α -> Prop) [Std.Irrefl r] (p : α -> Prop) : Std.Irrefl (Subrel r p) :=
  ⟨fun x => Std.Irrefl.irrefl (r := r) x⟩

instance (r : α -> α -> Prop) [Std.Trichotomous r] (p : α -> Prop) : Std.Trichotomous (Subrel r p) :=
  ⟨fun x y => by rw [Subtype.ext_iff]; exact @Std.Trichotomous.trichotomous α r _ x y⟩

instance (r : α -> α -> Prop) [IsWellFounded α r] (p : α -> Prop) : IsWellFounded _ (Subrel r p) :=
  (Subrel.relEmbedding r p).isWellFounded

instance (r : α -> α -> Prop) [IsPreorder α r] (p : α -> Prop) : IsPreorder _ (Subrel r p) where
instance (r : α -> α -> Prop) [IsStrictOrder α r] (p : α -> Prop) : IsStrictOrder _ (Subrel r p) where
instance (r : α -> α -> Prop) [IsWellOrder α r] (p : α -> Prop) : IsWellOrder _ (Subrel r p) where

end Subrel

/-- If a proposition holds for all elements, then the `Subrel` is equivalent to the original
relation. -/
@[simps! apply symm_apply]
/--
Definition of `RelIso.subrelUnivIso` / `RelIso.subrelUnivIso` 的定义

English:
definition RelIso.subrelUnivIso
  signature: {p : α -> Prop} (h : forall x, p x)
  body: Equiv.subtypeUnivEquiv h
  map_rel_iff' := by simp

中文:
定义 RelIso.subrelUnivIso
  签名: {p : α -> 命题} (h : 对任意 x, p x)
  定义体: Equiv.subtypeUnivEquiv h
  map_rel_iff' := by simp

Depends on / 依赖: Equiv.subtypeUnivEquiv, subtypeUnivEquiv
-/
def RelIso.subrelUnivIso {p : α -> Prop} (h : forall x, p x) : Subrel r p ≃r r where
  toEquiv := Equiv.subtypeUnivEquiv h
  map_rel_iff' := by simp

/--
Definition of `RelEmbedding.codRestrict` / `RelEmbedding.codRestrict` 的定义

English:
definition RelEmbedding.codRestrict
  signature: (p : Set β) (f : r ↪r s) (H : forall a, f a in p)
  body: ⟨f.toEmbedding.codRestrict p H, f.map_rel_iff'⟩

@[simp]

中文:
定义 关系嵌入.codRestrict
  签名: (p : 集合 β) (f : r ↪r s) (H : 对任意 a, f a in p)
  定义体: ⟨f.toEmbedding.codRestrict p H, f.map_rel_iff'⟩

@[simp]

Depends on / 依赖: codRestrict, f.map_rel_iff, f.toEmbedding.codRestrict, map_rel_iff, toEmbedding
-/
def RelEmbedding.codRestrict (p : Set β) (f : r ↪r s) (H : forall a, f a in p) : r ↪r Subrel s (· in p) :=
  ⟨f.toEmbedding.codRestrict p H, f.map_rel_iff'⟩

@[simp]
/--
theorem `RelEmbedding.codRestrict_apply` / 定理 `RelEmbedding.codRestrict_apply`

English:
theorem RelEmbedding.codRestrict_apply
  given: (p) (f : r ↪r s) (H a)
  proof: rfl

中文:
定理 关系嵌入.codRestrict_apply
  条件: (p) (f : r ↪r s) (H a)
  证明: rfl
-/
theorem RelEmbedding.codRestrict_apply (p) (f : r ↪r s) (H a) :
    RelEmbedding.codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

section image

/--
theorem `RelIso.image_eq_preimage_symm` / 定理 `RelIso.image_eq_preimage_symm`

English:
theorem RelIso.image_eq_preimage_symm
  given: (e : r ≃r s) (t : Set α)
  statement: e '' t = e.symm ⁻¹' t
  proof: e.toEquiv.image_eq_preimage_symm t

中文:
定理 RelIso.image_eq_preimage_symm
  条件: (e : r ≃r s) (t : 集合 α)
  结论: e '' t = e.symm ⁻¹' t
  证明: e.toEquiv.image_eq_preimage_symm t

Depends on / 依赖: e.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem RelIso.image_eq_preimage_symm (e : r ≃r s) (t : Set α) : e '' t = e.symm ⁻¹' t :=
  e.toEquiv.image_eq_preimage_symm t

/--
theorem `RelIso.preimage_eq_image_symm` / 定理 `RelIso.preimage_eq_image_symm`

English:
theorem RelIso.preimage_eq_image_symm
  given: (e : r ≃r s) (t : Set β)
  statement: e ⁻¹' t = e.symm '' t
  proof: by
  rw [e.symm.image_eq_preimage_symm]; rfl

中文:
定理 RelIso.preimage_eq_image_symm
  条件: (e : r ≃r s) (t : 集合 β)
  结论: e ⁻¹' t = e.symm '' t
  证明: by
  rw [e.symm.image_eq_preimage_symm]; rfl

Depends on / 依赖: e.symm.image_eq_preimage_symm, image_eq_preimage_symm
-/
theorem RelIso.preimage_eq_image_symm (e : r ≃r s) (t : Set β) : e ⁻¹' t = e.symm '' t := by
  rw [e.symm.image_eq_preimage_symm]; rfl

end image

/--
theorem `Acc.of_subrel` / 定理 `Acc.of_subrel`

English:
theorem Acc.of_subrel
  statement: {r : α -> α -> Prop} [IsTrans α r] {b : α} (a : { a // r a b })
  proof: h.recOn fun a _ IH => ⟨_, fun _ hb => IH ⟨_, _root_.trans hb a.2⟩ hb⟩

中文:
定理 Acc.of_subrel
  结论: {r : α -> α -> 命题} [是Trans α r] {b : α} (a : { a // r a b })
  证明: h.recOn fun a _ IH => ⟨_, fun _ hb => IH ⟨_, _root_.trans hb a.2⟩ hb⟩

Depends on / 依赖: _root_, _root_.trans, h.recOn
-/
theorem Acc.of_subrel {r : α -> α -> Prop} [IsTrans α r] {b : α} (a : { a // r a b })
    (h : Acc (Subrel r (r · b)) a) : Acc r a.1 :=
  h.recOn fun a _ IH => ⟨_, fun _ hb => IH ⟨_, _root_.trans hb a.2⟩ hb⟩

/--
theorem `wellFounded_iff_wellFounded_subrel` / 定理 `wellFounded_iff_wellFounded_subrel`

English:
theorem wellFounded_iff_wellFounded_subrel
  given: {r : α -> α -> Prop} [IsTrans α r]
  proof: InvImage.wf Subtype.val h
  mpr h := ⟨fun a => ⟨_, fun b hr => ((h a).apply _).of_subrel ⟨b, hr⟩⟩⟩

中文:
定理 wellFounded_iff_wellFounded_subrel
  条件: {r : α -> α -> 命题} [是Trans α r]
  证明: InvImage.wf Subtype.val h
  mpr h := ⟨fun a => ⟨_, fun b hr => ((h a).apply _).of_subrel ⟨b, hr⟩⟩⟩

Depends on / 依赖: InvImage, InvImage.wf, Subtype, Subtype.val
-/
theorem wellFounded_iff_wellFounded_subrel {r : α -> α -> Prop} [IsTrans α r] :
    WellFounded r ↔ forall b, WellFounded (Subrel r (r · b)) where
  mp h _ := InvImage.wf Subtype.val h
  mpr h := ⟨fun a => ⟨_, fun b hr => ((h a).apply _).of_subrel ⟨b, hr⟩⟩⟩
