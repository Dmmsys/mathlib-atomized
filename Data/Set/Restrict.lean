/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image

/-!
# Restrict the domain of a function to a set

## Main definitions

* `Set.domRestrict f s` : restrict the domain of `f` to the set `s`;
* `Set.codRestrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
-/

@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*} {π : α -> Type*}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Domain restriction -/
section domRestrict

/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: (s : Set α) (f : forall a : α, π a)
  body: fun x => f x

中文:
定义 domRestrict
  签名: (s : 集合 α) (f : 对任意 a : α, π a)
  定义体: fun x => f x
-/
def domRestrict (s : Set α) (f : forall a : α, π a) : forall a : s, π a := fun x => f x

/--
theorem `domRestrict_def` / 定理 `domRestrict_def`

English:
theorem domRestrict_def
  given: (s : Set α)
  statement: s.domRestrict (π := π) = fun f x => f x
  proof: rfl

中文:
定理 domRestrict_def
  条件: (s : 集合 α)
  结论: s.domRestrict (π := π) = fun f x => f x
  证明: rfl
-/
theorem domRestrict_def (s : Set α) : s.domRestrict (π := π) = fun f x => f x := rfl

/--
theorem `domRestrict_eq` / 定理 `domRestrict_eq`

English:
theorem domRestrict_eq
  given: (f : α -> β) (s : Set α)
  statement: s.domRestrict f = f ∘ Subtype.val
  proof: rfl

中文:
定理 domRestrict_eq
  条件: (f : α -> β) (s : 集合 α)
  结论: s.domRestrict f = f ∘ 子类型.val
  证明: rfl
-/
theorem domRestrict_eq (f : α -> β) (s : Set α) : s.domRestrict f = f ∘ Subtype.val :=
  rfl

/--
lemma `domRestrict_id` / 引理 `domRestrict_id`

English:
lemma domRestrict_id
  given: (s : Set α)
  statement: domRestrict s id = Subtype.val
  proof: rfl

@[simp, grind =]

中文:
引理 domRestrict_id
  条件: (s : 集合 α)
  结论: domRestrict s id = 子类型.val
  证明: rfl

@[simp, grind =]
-/
@[simp] lemma domRestrict_id (s : Set α) : domRestrict s id = Subtype.val := rfl

@[simp, grind =]
/--
theorem `domRestrict_apply` / 定理 `domRestrict_apply`

English:
theorem domRestrict_apply
  given: (f : (a : α) -> π a) (s : Set α) (x : s)
  statement: s.domRestrict f x = f x
  proof: rfl

中文:
定理 domRestrict_apply
  条件: (f : (a : α) -> π a) (s : 集合 α) (x : s)
  结论: s.domRestrict f x = f x
  证明: rfl
-/
theorem domRestrict_apply (f : (a : α) -> π a) (s : Set α) (x : s) : s.domRestrict f x = f x :=
  rfl

/--
theorem `domRestrict_eq_iff` / 定理 `domRestrict_eq_iff`

English:
theorem domRestrict_eq_iff
  given: {f : forall a, π a} {s : Set α} {g : forall a : s, π a}
  proof: funext_iff.trans Subtype.forall

中文:
定理 domRestrict_eq_iff
  条件: {f : 对任意 a, π a} {s : 集合 α} {g : 对任意 a : s, π a}
  证明: funext_iff.trans Subtype.forall

Depends on / 依赖: Subtype, Subtype.forall, funext_iff, funext_iff.trans
-/
theorem domRestrict_eq_iff {f : forall a, π a} {s : Set α} {g : forall a : s, π a} :
    domRestrict s f = g ↔ forall (a) (ha : a in s), f a = g ⟨a, ha⟩ :=
  funext_iff.trans Subtype.forall

/--
theorem `eq_domRestrict_iff` / 定理 `eq_domRestrict_iff`

English:
theorem eq_domRestrict_iff
  given: {s : Set α} {f : forall a : s, π a} {g : forall a, π a}
  proof: funext_iff.trans Subtype.forall

@[simp]

中文:
定理 eq_domRestrict_iff
  条件: {s : 集合 α} {f : 对任意 a : s, π a} {g : 对任意 a, π a}
  证明: funext_iff.trans Subtype.forall

@[simp]

Depends on / 依赖: Subtype, Subtype.forall, funext_iff, funext_iff.trans
-/
theorem eq_domRestrict_iff {s : Set α} {f : forall a : s, π a} {g : forall a, π a} :
    f = domRestrict s g ↔ forall (a) (ha : a in s), f ⟨a, ha⟩ = g a :=
  funext_iff.trans Subtype.forall

@[simp]
/--
theorem `range_domRestrict` / 定理 `range_domRestrict`

English:
theorem range_domRestrict
  given: (f : α -> β) (s : Set α)
  statement: Set.range (s.domRestrict f) = f '' s
  proof: (range_comp _ _).trans congr_arg (f '' ·) Subtype.range_coe

中文:
定理 range_domRestrict
  条件: (f : α -> β) (s : 集合 α)
  结论: 集合.range (s.domRestrict f) = f '' s
  证明: (range_comp _ _).trans congr_arg (f '' ·) Subtype.range_coe

Depends on / 依赖: Subtype, Subtype.range_coe, congr_arg, range_coe, range_comp
-/
theorem range_domRestrict (f : α -> β) (s : Set α) : Set.range (s.domRestrict f) = f '' s :=
(range_comp _ _).trans congr_arg (f '' ·) Subtype.range_coe

/--
theorem `image_domRestrict` / 定理 `image_domRestrict`

English:
theorem image_domRestrict
  given: (f : α -> β) (s t : Set α)
  proof: by
  rw [domRestrict_eq]; rw [image_comp]; rw [image_preimage_eq_inter_range]; rw [Subtype.range_coe]

@[simp]

中文:
定理 image_domRestrict
  条件: (f : α -> β) (s t : 集合 α)
  证明: by
  rw [domRestrict_eq]; rw [image_comp]; rw [image_preimage_eq_inter_range]; rw [Subtype.range_coe]

@[simp]

Depends on / 依赖: Subtype, Subtype.range_coe, domRestrict_eq, image_comp, image_preimage_eq_inter_range, range_coe
-/
theorem image_domRestrict (f : α -> β) (s t : Set α) :
    s.domRestrict f '' Subtype.val ⁻¹' t = f '' (t inter s) := by
  rw [domRestrict_eq]; rw [image_comp]; rw [image_preimage_eq_inter_range]; rw [Subtype.range_coe]

@[simp]
/--
theorem `domRestrict_dite` / 定理 `domRestrict_dite`

English:
theorem domRestrict_dite
  statement: {s : Set α} [forall x, Decidable (x in s)] (f : forall a in s, β)
  proof: funext fun a => dif_pos a.2

@[simp]

中文:
定理 domRestrict_dite
  结论: {s : 集合 α} [对任意 x, 可判定 (x in s)] (f : 对任意 a in s, β)
  证明: funext fun a => dif_pos a.2

@[simp]

Depends on / 依赖: dif_pos
-/
theorem domRestrict_dite {s : Set α} [forall x, Decidable (x in s)] (f : forall a in s, β)
    (g : forall a ∉ s, β) :
    (s.domRestrict fun a => if h : a in s then f a h else g a h) = (fun a : s => f a a.2) :=
  funext fun a => dif_pos a.2

@[simp]
/--
theorem `domRestrict_dite_compl` / 定理 `domRestrict_dite_compl`

English:
theorem domRestrict_dite_compl
  statement: {s : Set α} [forall x, Decidable (x in s)] (f : forall a in s, β)
  proof: funext fun a => dif_neg a.2

@[simp]

中文:
定理 domRestrict_dite_compl
  结论: {s : 集合 α} [对任意 x, 可判定 (x in s)] (f : 对任意 a in s, β)
  证明: funext fun a => dif_neg a.2

@[simp]

Depends on / 依赖: dif_neg
-/
theorem domRestrict_dite_compl {s : Set α} [forall x, Decidable (x in s)] (f : forall a in s, β)
    (g : forall a ∉ s, β) :
    (sᶜ.domRestrict fun a => if h : a in s then f a h else g a h) =
      (fun a : (sᶜ : Set α) => g a a.2) :=
  funext fun a => dif_neg a.2

@[simp]
/--
theorem `domRestrict_ite` / 定理 `domRestrict_ite`

English:
theorem domRestrict_ite
  given: (f g : α -> β) (s : Set α) [forall x, Decidable (x in s)]
  proof: domRestrict_dite _ _

@[simp]

中文:
定理 domRestrict_ite
  条件: (f g : α -> β) (s : 集合 α) [对任意 x, 可判定 (x in s)]
  证明: domRestrict_dite _ _

@[simp]

Depends on / 依赖: domRestrict_dite
-/
theorem domRestrict_ite (f g : α -> β) (s : Set α) [forall x, Decidable (x in s)] :
    (s.domRestrict fun a => if a in s then f a else g a) = s.domRestrict f := domRestrict_dite _ _

@[simp]
/--
theorem `domRestrict_ite_compl` / 定理 `domRestrict_ite_compl`

English:
theorem domRestrict_ite_compl
  given: (f g : α -> β) (s : Set α) [forall x, Decidable (x in s)]
  proof: domRestrict_dite_compl _ _

@[simp]

中文:
定理 domRestrict_ite_compl
  条件: (f g : α -> β) (s : 集合 α) [对任意 x, 可判定 (x in s)]
  证明: domRestrict_dite_compl _ _

@[simp]

Depends on / 依赖: domRestrict_dite_compl
-/
theorem domRestrict_ite_compl (f g : α -> β) (s : Set α) [forall x, Decidable (x in s)] :
    (sᶜ.domRestrict fun a => if a in s then f a else g a) = sᶜ.domRestrict g :=
  domRestrict_dite_compl _ _

@[simp]
/--
theorem `domRestrict_piecewise` / 定理 `domRestrict_piecewise`

English:
theorem domRestrict_piecewise
  given: (f g : α -> β) (s : Set α) [forall x, Decidable (x in s)]
  proof: domRestrict_ite _ _ _

@[simp]

中文:
定理 domRestrict_piecewise
  条件: (f g : α -> β) (s : 集合 α) [对任意 x, 可判定 (x in s)]
  证明: domRestrict_ite _ _ _

@[simp]

Depends on / 依赖: domRestrict_ite
-/
theorem domRestrict_piecewise (f g : α -> β) (s : Set α) [forall x, Decidable (x in s)] :
    s.domRestrict (piecewise s f g) = s.domRestrict f := domRestrict_ite _ _ _

@[simp]
/--
theorem `domRestrict_piecewise_compl` / 定理 `domRestrict_piecewise_compl`

English:
theorem domRestrict_piecewise_compl
  given: (f g : α -> β) (s : Set α) [forall x, Decidable (x in s)]
  proof: domRestrict_ite_compl _ _ _

中文:
定理 domRestrict_piecewise_compl
  条件: (f g : α -> β) (s : 集合 α) [对任意 x, 可判定 (x in s)]
  证明: domRestrict_ite_compl _ _ _

Depends on / 依赖: domRestrict_ite_compl
-/
theorem domRestrict_piecewise_compl (f g : α -> β) (s : Set α) [forall x, Decidable (x in s)] :
    sᶜ.domRestrict (piecewise s f g) = sᶜ.domRestrict g := domRestrict_ite_compl _ _ _

/--
theorem `domRestrict_extend_range` / 定理 `domRestrict_extend_range`

English:
theorem domRestrict_extend_range
  given: (f : α -> β) (g : α -> γ) (g' : β -> γ)
  proof: by
  classical
  exact domRestrict_dite _ _

@[simp]

中文:
定理 domRestrict_extend_range
  条件: (f : α -> β) (g : α -> γ) (g' : β -> γ)
  证明: by
  classical
  exact domRestrict_dite _ _

@[simp]

Depends on / 依赖: classical, domRestrict_dite
-/
theorem domRestrict_extend_range (f : α -> β) (g : α -> γ) (g' : β -> γ) :
    (range f).domRestrict (extend f g g') = fun x => g x.coe_prop.choose := by
  classical
  exact domRestrict_dite _ _

@[simp]
/--
theorem `domRestrict_extend_compl_range` / 定理 `domRestrict_extend_compl_range`

English:
theorem domRestrict_extend_compl_range
  given: (f : α -> β) (g : α -> γ) (g' : β -> γ)
  proof: by
  classical
  exact domRestrict_dite_compl _ _

中文:
定理 domRestrict_extend_compl_range
  条件: (f : α -> β) (g : α -> γ) (g' : β -> γ)
  证明: by
  classical
  exact domRestrict_dite_compl _ _

Depends on / 依赖: classical, domRestrict_dite_compl
-/
theorem domRestrict_extend_compl_range (f : α -> β) (g : α -> γ) (g' : β -> γ) :
    (range f)ᶜ.domRestrict (extend f g g') = g' ∘ Subtype.val := by
  classical
  exact domRestrict_dite_compl _ _

/-- If a function `f` is restricted to a set `t`, and `s ⊆ t`, this is the restriction to `s`. -/
@[simp]
/--
Definition of `domRestrict₂` / `domRestrict₂` 的定义

English:
definition domRestrict₂
  signature: {s t : Set α} (hst : s subseteq t) (f : forall a : t, π a)
  body: fun x => f ⟨x.1, hst x.2⟩

中文:
定义 domRestrict₂
  签名: {s t : 集合 α} (hst : s subseteq t) (f : 对任意 a : t, π a)
  定义体: fun x => f ⟨x.1, hst x.2⟩
-/
def domRestrict₂ {s t : Set α} (hst : s subseteq t) (f : forall a : t, π a) : forall a : s, π a :=
  fun x => f ⟨x.1, hst x.2⟩

/--
theorem `domRestrict₂_def` / 定理 `domRestrict₂_def`

English:
theorem domRestrict₂_def
  given: {s t : Set α} (hst : s subseteq t)
  proof: rfl

中文:
定理 domRestrict₂_def
  条件: {s t : 集合 α} (hst : s subseteq t)
  证明: rfl
-/
theorem domRestrict₂_def {s t : Set α} (hst : s subseteq t) :
    domRestrict₂ (π := π) hst = fun f x => f ⟨x.1, hst x.2⟩ := rfl

/--
theorem `domRestrict₂_comp_domRestrict` / 定理 `domRestrict₂_comp_domRestrict`

English:
theorem domRestrict₂_comp_domRestrict
  given: {s t : Set α} (hst : s subseteq t)
  proof: rfl

中文:
定理 domRestrict₂_comp_domRestrict
  条件: {s t : 集合 α} (hst : s subseteq t)
  证明: rfl

Depends on / 依赖: domRestrict, s.domRestrict, t.domRestrict
-/
theorem domRestrict₂_comp_domRestrict {s t : Set α} (hst : s subseteq t) :
    (domRestrict₂ (π := π) hst) ∘ t.domRestrict = s.domRestrict := rfl

/--
theorem `domRestrict₂_comp_domRestrict₂` / 定理 `domRestrict₂_comp_domRestrict₂`

English:
theorem domRestrict₂_comp_domRestrict₂
  given: {s t u : Set α} (hst : s subseteq t) (htu : t subseteq u)
  proof: rfl

中文:
定理 domRestrict₂_comp_domRestrict₂
  条件: {s t u : 集合 α} (hst : s subseteq t) (htu : t subseteq u)
  证明: rfl

Depends on / 依赖: hst.trans
-/
theorem domRestrict₂_comp_domRestrict₂ {s t u : Set α} (hst : s subseteq t) (htu : t subseteq u) :
    (domRestrict₂ (π := π) hst) ∘ (domRestrict₂ htu) = domRestrict₂ (hst.trans htu) := rfl

/--
theorem `range_extend_subset` / 定理 `range_extend_subset`

English:
theorem range_extend_subset
  given: (f : α -> β) (g : α -> γ) (g' : β -> γ)
  proof: by
  classical
  rintro _ ⟨y, rfl⟩
  rw [extend_def]
  split_ifs with h
  exacts [Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]

中文:
定理 range_extend_subset
  条件: (f : α -> β) (g : α -> γ) (g' : β -> γ)
  证明: by
  classical
  rintro _ ⟨y, rfl⟩
  rw [extend_def]
  split_ifs with h
  exacts [Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]

Depends on / 依赖: Or.inl, Or.inr, classical, exacts, extend_def, mem_image_of_mem, mem_range_self, split_ifs
-/
theorem range_extend_subset (f : α -> β) (g : α -> γ) (g' : β -> γ) :
    range (extend f g g') subseteq range g union g' '' (range f)ᶜ := by
  classical
  rintro _ ⟨y, rfl⟩
  rw [extend_def]
  split_ifs with h
  exacts [Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]

/--
theorem `range_extend` / 定理 `range_extend`

English:
theorem range_extend
  given: {f : α -> β} (hf : Injective f) (g : α -> γ) (g' : β -> γ)
  proof: by
  refine (range_extend_subset _ _ _).antisymm ?_
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts [⟨f x, hf.extend_apply _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]

中文:
定理 range_extend
  条件: {f : α -> β} (hf : 单射 f) (g : α -> γ) (g' : β -> γ)
  证明: by
  refine (range_extend_subset _ _ _).antisymm ?_
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts [⟨f x, hf.extend_apply _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]

Depends on / 依赖: antisymm, exacts, extend_apply, hf.extend_apply, range_extend_subset
-/
theorem range_extend {f : α -> β} (hf : Injective f) (g : α -> γ) (g' : β -> γ) :
    range (extend f g g') = range g union g' '' (range f)ᶜ := by
  refine (range_extend_subset _ _ _).antisymm ?_
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts [⟨f x, hf.extend_apply _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]

/--
lemma `_root_.Function.FactorsThrough.extend_injOn` / 引理 `_root_.Function.FactorsThrough.extend_injOn`

English:
lemma _root_.Function.FactorsThrough.extend_injOn
  statement: {f : α -> β} {g : α -> γ} {j : β -> γ}
  proof: by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
  rw [hf.extend_apply]; rw [hf.extend_apply] at heq
  rw [hg heq]

中文:
引理 _root_.函数.FactorsThrough.extend_injOn
  结论: {f : α -> β} {g : α -> γ} {j : β -> γ}
  证明: by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
  rw [hf.extend_apply]; rw [hf.extend_apply] at heq
  rw [hg heq]

Depends on / 依赖: extend_apply, hf.extend_apply
-/
lemma _root_.Function.FactorsThrough.extend_injOn {f : α -> β} {g : α -> γ} {j : β -> γ}
    (hf : g.FactorsThrough f) (hg : g.Injective) :
    (range f).InjOn (extend f g j) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
  rw [hf.extend_apply]; rw [hf.extend_apply] at heq
  rw [hg heq]

/--
lemma `_root_.Function.Injective.extend_injOn` / 引理 `_root_.Function.Injective.extend_injOn`

English:
lemma _root_.Function.Injective.extend_injOn
  statement: {f : α -> β} {g : α -> γ} {j : β -> γ}
  proof: (hf.factorsThrough g).extend_injOn hg

中文:
引理 _root_.函数.单射.extend_injOn
  结论: {f : α -> β} {g : α -> γ} {j : β -> γ}
  证明: (hf.factorsThrough g).extend_injOn hg

Depends on / 依赖: extend_injOn, factorsThrough, hf.factorsThrough
-/
lemma _root_.Function.Injective.extend_injOn {f : α -> β} {g : α -> γ} {j : β -> γ}
    (hf : f.Injective) (hg : g.Injective) :
    (range f).InjOn (extend f g j) :=
  (hf.factorsThrough g).extend_injOn hg

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : ι -> α) (s : Set α) (h : forall x, f x in s)
  body: fun x => ⟨f x, h x⟩

@[simp]

中文:
定义 codRestrict
  签名: (f : ι -> α) (s : 集合 α) (h : 对任意 x, f x in s)
  定义体: fun x => ⟨f x, h x⟩

@[simp]
-/
def codRestrict (f : ι -> α) (s : Set α) (h : forall x, f x in s) : ι -> s := fun x => ⟨f x, h x⟩

@[simp]
/--
theorem `val_codRestrict_apply` / 定理 `val_codRestrict_apply`

English:
theorem val_codRestrict_apply
  given: (f : ι -> α) (s : Set α) (h : forall x, f x in s) (x : ι)
  proof: rfl

@[simp]

中文:
定理 val_codRestrict_apply
  条件: (f : ι -> α) (s : 集合 α) (h : 对任意 x, f x in s) (x : ι)
  证明: rfl

@[simp]
-/
theorem val_codRestrict_apply (f : ι -> α) (s : Set α) (h : forall x, f x in s) (x : ι) :
    (codRestrict f s h x : α) = f x :=
  rfl

@[simp]
/--
theorem `domRestrict_comp_codRestrict` / 定理 `domRestrict_comp_codRestrict`

English:
theorem domRestrict_comp_codRestrict
  statement: {f : ι -> α} {g : α -> β} {b : Set α}
  proof: rfl

@[simp]

中文:
定理 domRestrict_comp_codRestrict
  结论: {f : ι -> α} {g : α -> β} {b : 集合 α}
  证明: rfl

@[simp]
-/
theorem domRestrict_comp_codRestrict {f : ι -> α} {g : α -> β} {b : Set α}
    (h : forall x, f x in b) : b.domRestrict g ∘ b.codRestrict f h = g ∘ f :=
  rfl

@[simp]
/--
theorem `injective_codRestrict` / 定理 `injective_codRestrict`

English:
theorem injective_codRestrict
  given: {f : ι -> α} {s : Set α} (h : forall x, f x in s)
  proof: by
  simp only [Injective, Subtype.ext_iff, val_codRestrict_apply]

alias ⟨_, _root_.Function.Injective.codRestrict⟩ := injective_codRestrict

中文:
定理 injective_codRestrict
  条件: {f : ι -> α} {s : 集合 α} (h : 对任意 x, f x in s)
  证明: by
  simp only [Injective, Subtype.ext_iff, val_codRestrict_apply]

alias ⟨_, _root_.Function.Injective.codRestrict⟩ := injective_codRestrict

Depends on / 依赖: Injective, Subtype, Subtype.ext_iff, ext_iff, val_codRestrict_apply
-/
theorem injective_codRestrict {f : ι -> α} {s : Set α} (h : forall x, f x in s) :
    Injective (codRestrict f s h) ↔ Injective f := by
  simp only [Injective, Subtype.ext_iff, val_codRestrict_apply]

alias ⟨_, _root_.Function.Injective.codRestrict⟩ := injective_codRestrict

/--
theorem `range_codRestrict` / 定理 `range_codRestrict`

English:
theorem range_codRestrict
  given: {f : ι -> α} {s : Set α} (h : forall x, f x in s)
  proof: by
  ext; simp [Subtype.ext_iff]

中文:
定理 range_codRestrict
  条件: {f : ι -> α} {s : 集合 α} (h : 对任意 x, f x in s)
  证明: by
  ext; simp [Subtype.ext_iff]
-/
@[simp] theorem range_codRestrict {f : ι -> α} {s : Set α} (h : forall x, f x in s) :
    range (s.codRestrict f h) = (↑) ⁻¹' range f := by
  ext; simp [Subtype.ext_iff]

/--
theorem `surjective_codRestrict` / 定理 `surjective_codRestrict`

English:
theorem surjective_codRestrict
  given: {f : ι -> α} {s : Set α} (h : forall x, f x in s)
  proof: by
  simp [← range_eq_univ, Subset.antisymm_iff (a := range f), range_subset_iff, h]

中文:
定理 surjective_codRestrict
  条件: {f : ι -> α} {s : 集合 α} (h : 对任意 x, f x in s)
  证明: by
  simp [← range_eq_univ, Subset.antisymm_iff (a := range f), range_subset_iff, h]

Depends on / 依赖: Subset, Subset.antisymm_iff, antisymm_iff, range_eq_univ, range_subset_iff
-/
theorem surjective_codRestrict {f : ι -> α} {s : Set α} (h : forall x, f x in s) :
    (s.codRestrict f h).Surjective ↔ range f = s := by
  simp [← range_eq_univ, Subset.antisymm_iff (a := range f), range_subset_iff, h]

/--
theorem `codRestrict_range_surjective` / 定理 `codRestrict_range_surjective`

English:
theorem codRestrict_range_surjective
  given: (f : ι -> α)
  proof: by
  rintro ⟨b, ⟨a, rfl⟩⟩
  exact ⟨a, rfl⟩

中文:
定理 codRestrict_range_surjective
  条件: (f : ι -> α)
  证明: by
  rintro ⟨b, ⟨a, rfl⟩⟩
  exact ⟨a, rfl⟩
-/
theorem codRestrict_range_surjective (f : ι -> α) :
    ((range f).codRestrict f mem_range_self).Surjective := by
  rintro ⟨b, ⟨a, rfl⟩⟩
  exact ⟨a, rfl⟩

variable {s : Set α} {f₁ f₂ : α -> β}

@[simp]
/--
theorem `domRestrict_eq_domRestrict_iff` / 定理 `domRestrict_eq_domRestrict_iff`

English:
theorem domRestrict_eq_domRestrict_iff
  proof: domRestrict_eq_iff

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_def := domRestrict_def
@[deprecated (since := "2026-07-19")] alias restrict_eq := domRestrict_eq
@[deprecated (since := "2026-07-19")] alias restrict_id := dom

中文:
定理 domRestrict_eq_domRestrict_iff
  证明: domRestrict_eq_iff

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_def := domRestrict_def
@[deprecated (since := "2026-07-19")] alias restrict_eq := domRestrict_eq
@[deprecated (since := "2026-07-19")] alias restrict_id := dom

Depends on / 依赖: domRestrict_eq_iff
-/
theorem domRestrict_eq_domRestrict_iff :
    domRestrict s f₁ = domRestrict s f₂ ↔ EqOn f₁ f₂ s := domRestrict_eq_iff

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_def := domRestrict_def
@[deprecated (since := "2026-07-19")] alias restrict_eq := domRestrict_eq
@[deprecated (since := "2026-07-19")] alias restrict_id := domRestrict_id
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")] alias restrict_eq_iff := domRestrict_eq_iff
@[deprecated (since := "2026-07-19")] alias eq_restrict_iff := eq_domRestrict_iff
@[deprecated (since := "2026-07-19")] alias range_restrict := range_domRestrict
@[deprecated (since := "2026-07-19")] alias image_restrict := image_domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_dite := domRestrict_dite
@[deprecated (since := "2026-07-19")] alias restrict_dite_compl := domRestrict_dite_compl
@[deprecated (since := "2026-07-19")] alias restrict_ite := domRestrict_ite
@[deprecated (since := "2026-07-19")] alias restrict_ite_compl := domRestrict_ite_compl
@[deprecated (since := "2026-07-19")] alias restrict_piecewise := domRestrict_piecewise
@[deprecated (since := "2026-07-19")] alias restrict_piecewise_compl := domRestrict_piecewise_compl
@[deprecated (since := "2026-07-19")] alias restrict_extend_range := domRestrict_extend_range
@[deprecated (since := "2026-07-19")]
alias restrict_extend_compl_range := domRestrict_extend_compl_range
@[deprecated (since := "2026-07-19")] alias restrict₂ := domRestrict₂
@[deprecated (since := "2026-07-19")] alias restrict₂_def := domRestrict₂_def
@[deprecated (since := "2026-07-19")] alias restrict₂_comp_restrict := domRestrict₂_comp_domRestrict
@[deprecated (since := "2026-07-19")]
alias restrict₂_comp_restrict₂ := domRestrict₂_comp_domRestrict₂
@[deprecated (since := "2026-07-19")]
alias restrict_comp_codRestrict := domRestrict_comp_codRestrict
@[deprecated (since := "2026-07-19")]
alias restrict_eq_restrict_iff := domRestrict_eq_domRestrict_iff

end domRestrict

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ : α -> β} {g g₁ g₂ : β -> γ}
  {f' f₁' f₂' : β -> α} {g' : γ -> β} {a : α} {b : β}

section MapsTo

/--
theorem `MapsTo.restrict_commutes` / 定理 `MapsTo.restrict_commutes`

English:
theorem MapsTo.restrict_commutes
  given: (f : α -> β) (s : Set α) (t : Set β) (h : MapsTo f s t)
  proof: rfl

@[simp]

中文:
定理 映射到.restrict_commutes
  条件: (f : α -> β) (s : 集合 α) (t : 集合 β) (h : 映射到 f s t)
  证明: rfl

@[simp]
-/
theorem MapsTo.restrict_commutes (f : α -> β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    Subtype.val ∘ h.restrict f s t = f ∘ Subtype.val :=
  rfl

@[simp]
/--
theorem `MapsTo.val_restrict_apply` / 定理 `MapsTo.val_restrict_apply`

English:
theorem MapsTo.val_restrict_apply
  given: (h : MapsTo f s t) (x : s)
  statement: (h.restrict f s t x : β) = f x
  proof: rfl

中文:
定理 映射到.val_restrict_apply
  条件: (h : 映射到 f s t) (x : s)
  结论: (h.restrict f s t x : β) = f x
  证明: rfl
-/
theorem MapsTo.val_restrict_apply (h : MapsTo f s t) (x : s) : (h.restrict f s t x : β) = f x :=
  rfl

/--
theorem `MapsTo.coe_iterate_restrict` / 定理 `MapsTo.coe_iterate_restrict`

English:
theorem MapsTo.coe_iterate_restrict
  given: {f : α -> α} (h : MapsTo f s s) (x : s) (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih => simp only [iterate_succ', comp_apply, val_restrict_apply, ih]

中文:
定理 映射到.coe_iterate_restrict
  条件: {f : α -> α} (h : 映射到 f s s) (x : s) (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih => simp only [iterate_succ', comp_apply, val_restrict_apply, ih]

Depends on / 依赖: comp_apply, iterate_succ, val_restrict_apply
-/
theorem MapsTo.coe_iterate_restrict {f : α -> α} (h : MapsTo f s s) (x : s) (k : Nat) :
    h.restrict^[k] x = f^[k] x := by
  induction k with
  | zero => simp
  | succ k ih => simp only [iterate_succ', comp_apply, val_restrict_apply, ih]

/-- Restricting the domain and then the codomain is the same as `MapsTo.restrict`. -/
@[simp]
/--
theorem `codRestrict_domRestrict` / 定理 `codRestrict_domRestrict`

English:
theorem codRestrict_domRestrict
  given: (h : forall x : s, f x in t)
  proof: rfl

@[deprecated (since := "2026-07-19")] alias codRestrict_restrict := codRestrict_domRestrict

中文:
定理 codRestrict_domRestrict
  条件: (h : 对任意 x : s, f x in t)
  证明: rfl

@[deprecated (since := "2026-07-19")] alias codRestrict_restrict := codRestrict_domRestrict
-/
theorem codRestrict_domRestrict (h : forall x : s, f x in t) :
    codRestrict (s.domRestrict f) t h = MapsTo.restrict f s t fun x hx => h ⟨x, hx⟩ :=
  rfl

@[deprecated (since := "2026-07-19")] alias codRestrict_restrict := codRestrict_domRestrict

/--
theorem `MapsTo.restrict_eq_codRestrict` / 定理 `MapsTo.restrict_eq_codRestrict`

English:
theorem MapsTo.restrict_eq_codRestrict
  given: (h : MapsTo f s t)
  proof: rfl

中文:
定理 映射到.restrict_eq_codRestrict
  条件: (h : 映射到 f s t)
  证明: rfl
-/
theorem MapsTo.restrict_eq_codRestrict (h : MapsTo f s t) :
    h.restrict f s t = codRestrict (s.domRestrict f) t fun x => h x.2 :=
  rfl

/--
theorem `MapsTo.coe_restrict` / 定理 `MapsTo.coe_restrict`

English:
theorem MapsTo.coe_restrict
  given: (h : Set.MapsTo f s t)
  proof: rfl

中文:
定理 映射到.coe_restrict
  条件: (h : 集合.映射到 f s t)
  证明: rfl
-/
theorem MapsTo.coe_restrict (h : Set.MapsTo f s t) :
    Subtype.val ∘ h.restrict f s t = s.domRestrict f :=
  rfl

/--
theorem `MapsTo.range_restrict` / 定理 `MapsTo.range_restrict`

English:
theorem MapsTo.range_restrict
  given: (f : α -> β) (s : Set α) (t : Set β) (h : MapsTo f s t)
  proof: Set.range_subtype_map f h

中文:
定理 映射到.range_restrict
  条件: (f : α -> β) (s : 集合 α) (t : 集合 β) (h : 映射到 f s t)
  证明: Set.range_subtype_map f h

Depends on / 依赖: Set.range_subtype_map, range_subtype_map
-/
theorem MapsTo.range_restrict (f : α -> β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    range (h.restrict f s t) = Subtype.val ⁻¹' f '' s :=
  Set.range_subtype_map f h

/--
theorem `mapsTo_iff_exists_map_subtype` / 定理 `mapsTo_iff_exists_map_subtype`

English:
theorem mapsTo_iff_exists_map_subtype
  statement: MapsTo f s t ↔ exists g : s -> t, forall x : s, f x = g x
  proof: ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx => by
    rw [hg ⟨x]; rw [hx⟩]
    apply Subtype.coe_prop⟩

中文:
定理 mapsTo_iff_存在_map_subtype
  结论: 映射到 f s t ↔ 存在 g : s -> t, 对任意 x : s, f x = g x
  证明: ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx => by
    rw [hg ⟨x]; rw [hx⟩]
    apply Subtype.coe_prop⟩

Depends on / 依赖: Subtype, Subtype.coe_prop, coe_prop, h.restrict, restrict
-/
theorem mapsTo_iff_exists_map_subtype : MapsTo f s t ↔ exists g : s -> t, forall x : s, f x = g x :=
  ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx => by
    rw [hg ⟨x]; rw [hx⟩]
    apply Subtype.coe_prop⟩

/--
theorem `surjective_mapsTo_image_restrict` / 定理 `surjective_mapsTo_image_restrict`

English:
theorem surjective_mapsTo_image_restrict
  given: (f : α -> β) (s : Set α)
  proof: fun ⟨_, x, hs, hxy⟩ =>
  ⟨⟨x, hs⟩, Subtype.ext hxy⟩

中文:
定理 surjective_mapsTo_image_restrict
  条件: (f : α -> β) (s : 集合 α)
  证明: fun ⟨_, x, hs, hxy⟩ =>
  ⟨⟨x, hs⟩, Subtype.ext hxy⟩
-/
theorem surjective_mapsTo_image_restrict (f : α -> β) (s : Set α) :
    Surjective ((mapsTo_image f s).restrict f s (f '' s)) := fun ⟨_, x, hs, hxy⟩ =>
  ⟨⟨x, hs⟩, Subtype.ext hxy⟩

end MapsTo

/-! ### Restriction onto preimage -/
section

variable (t)

variable (f s) in
/--
theorem `image_restrictPreimage` / 定理 `image_restrictPreimage`

English:
theorem image_restrictPreimage
  proof: by
  delta Set.restrictPreimage
  rw [← (Subtype.coe_injective).image_injective.eq_iff]; rw [← image_comp]; rw [MapsTo.restrict_commutes]; rw [image_comp]; rw [Subtype.image_preimage_coe]; rw [Subtype.image_preimage_coe]; rw [image_preimage_inter]

中文:
定理 image_restrictPreimage
  证明: by
  delta Set.restrictPreimage
  rw [← (Subtype.coe_injective).image_injective.eq_iff]; rw [← image_comp]; rw [MapsTo.restrict_commutes]; rw [image_comp]; rw [Subtype.image_preimage_coe]; rw [Subtype.image_preimage_coe]; rw [image_preimage_inter]

Depends on / 依赖: MapsTo, MapsTo.restrict_commutes, Set.restrictPreimage, Subtype, Subtype.coe_injective, Subtype.image_preimage_coe, coe_injective, eq_iff, image_comp, image_injective, image_injective.eq_iff, image_preimage_coe, image_preimage_inter, restrictPreimage, restrict_commutes
-/
theorem image_restrictPreimage :
    t.restrictPreimage f '' Subtype.val ⁻¹' s = Subtype.val ⁻¹' f '' s := by
  delta Set.restrictPreimage
  rw [← (Subtype.coe_injective).image_injective.eq_iff]; rw [← image_comp]; rw [MapsTo.restrict_commutes]; rw [image_comp]; rw [Subtype.image_preimage_coe]; rw [Subtype.image_preimage_coe]; rw [image_preimage_inter]

variable (f) in
/--
theorem `range_restrictPreimage` / 定理 `range_restrictPreimage`

English:
theorem range_restrictPreimage
  statement: range (t.restrictPreimage f) = Subtype.val ⁻¹' range f
  proof: by
  simp only [← image_univ, ← image_restrictPreimage, preimage_univ]

@[simp]

中文:
定理 range_restrictPreimage
  结论: range (t.restrictPreimage f) = 子类型.val ⁻¹' range f
  证明: by
  simp only [← image_univ, ← image_restrictPreimage, preimage_univ]

@[simp]

Depends on / 依赖: image_restrictPreimage, image_univ, preimage_univ
-/
theorem range_restrictPreimage : range (t.restrictPreimage f) = Subtype.val ⁻¹' range f := by
  simp only [← image_univ, ← image_restrictPreimage, preimage_univ]

@[simp]
/--
theorem `restrictPreimage_mk` / 定理 `restrictPreimage_mk`

English:
theorem restrictPreimage_mk
  given: (h : a in f ⁻¹' t)
  statement: t.restrictPreimage f ⟨a, h⟩ = ⟨f a, h⟩
  proof: rfl

中文:
定理 restrictPreimage_mk
  条件: (h : a in f ⁻¹' t)
  结论: t.restrictPreimage f ⟨a, h⟩ = ⟨f a, h⟩
  证明: rfl
-/
theorem restrictPreimage_mk (h : a in f ⁻¹' t) : t.restrictPreimage f ⟨a, h⟩ = ⟨f a, h⟩ := rfl

/--
theorem `image_val_preimage_restrictPreimage` / 定理 `image_val_preimage_restrictPreimage`

English:
theorem image_val_preimage_restrictPreimage
  given: {u : Set t}
  proof: by
  ext
  simp

中文:
定理 image_val_preimage_restrictPreimage
  条件: {u : 集合 t}
  证明: by
  ext
  simp
-/
theorem image_val_preimage_restrictPreimage {u : Set t} :
    Subtype.val '' t.restrictPreimage f ⁻¹' u = f ⁻¹' Subtype.val '' u := by
  ext
  simp

/--
theorem `preimage_restrictPreimage` / 定理 `preimage_restrictPreimage`

English:
theorem preimage_restrictPreimage
  given: {u : Set t}
  proof: by
  rw [← preimage_preimage (g := f) (f := Subtype.val)]; rw [← image_val_preimage_restrictPreimage]; rw [preimage_image_eq _ Subtype.val_injective]

中文:
定理 preimage_restrictPreimage
  条件: {u : 集合 t}
  证明: by
  rw [← preimage_preimage (g := f) (f := Subtype.val)]; rw [← image_val_preimage_restrictPreimage]; rw [preimage_image_eq _ Subtype.val_injective]

Depends on / 依赖: Subtype, Subtype.val, Subtype.val_injective, image_val_preimage_restrictPreimage, preimage_image_eq, preimage_preimage, val_injective
-/
theorem preimage_restrictPreimage {u : Set t} :
    t.restrictPreimage f ⁻¹' u = (fun a : f ⁻¹' t => f a) ⁻¹' Subtype.val '' u := by
  rw [← preimage_preimage (g := f) (f := Subtype.val)]; rw [← image_val_preimage_restrictPreimage]; rw [preimage_image_eq _ Subtype.val_injective]

/--
lemma `restrictPreimage_injective` / 引理 `restrictPreimage_injective`

English:
lemma restrictPreimage_injective
  given: (hf : Injective f)
  statement: Injective (t.restrictPreimage f)
  proof: fun _ _ e => Subtype.coe_injective hf Subtype.mk.inj e

中文:
引理 restrictPreimage_injective
  条件: (hf : 单射 f)
  结论: 单射 (t.restrictPreimage f)
  证明: fun _ _ e => Subtype.coe_injective hf Subtype.mk.inj e

Depends on / 依赖: Subtype, Subtype.coe_injective, Subtype.mk.inj, coe_injective
-/
lemma restrictPreimage_injective (hf : Injective f) : Injective (t.restrictPreimage f) :=
fun _ _ e => Subtype.coe_injective hf Subtype.mk.inj e

/--
lemma `restrictPreimage_surjective` / 引理 `restrictPreimage_surjective`

English:
lemma restrictPreimage_surjective
  given: (hf : Surjective f)
  statement: Surjective (t.restrictPreimage f)
  proof: fun x => ⟨⟨_, ((hf x).choose_spec.symm ▸ x.2 : _ in t)⟩, Subtype.ext (hf x).choose_spec⟩

中文:
引理 restrictPreimage_surjective
  条件: (hf : 满射 f)
  结论: 满射 (t.restrictPreimage f)
  证明: fun x => ⟨⟨_, ((hf x).choose_spec.symm ▸ x.2 : _ in t)⟩, Subtype.ext (hf x).choose_spec⟩

Depends on / 依赖: Subtype, Subtype.ext, choose_spec, choose_spec.symm
-/
lemma restrictPreimage_surjective (hf : Surjective f) : Surjective (t.restrictPreimage f) :=
  fun x => ⟨⟨_, ((hf x).choose_spec.symm ▸ x.2 : _ in t)⟩, Subtype.ext (hf x).choose_spec⟩

/--
lemma `restrictPreimage_bijective` / 引理 `restrictPreimage_bijective`

English:
lemma restrictPreimage_bijective
  given: (hf : Bijective f)
  statement: Bijective (t.restrictPreimage f)
  proof: ⟨t.restrictPreimage_injective hf.1, t.restrictPreimage_surjective hf.2⟩

alias _root_.Function.Injective.restrictPreimage := Set.restrictPreimage_injective
alias _root_.Function.Surjective.restrictPreimage := Set.restrictPreimage_surjective
alias _root_.Function.Bijective.restrictPreimage := Set.res

中文:
引理 restrictPreimage_bijective
  条件: (hf : 双射 f)
  结论: 双射 (t.restrictPreimage f)
  证明: ⟨t.restrictPreimage_injective hf.1, t.restrictPreimage_surjective hf.2⟩

alias _root_.Function.Injective.restrictPreimage := Set.restrictPreimage_injective
alias _root_.Function.Surjective.restrictPreimage := Set.restrictPreimage_surjective
alias _root_.Function.Bijective.restrictPreimage := Set.res

Depends on / 依赖: restrictPreimage_injective, restrictPreimage_surjective, t.restrictPreimage_injective, t.restrictPreimage_surjective
-/
lemma restrictPreimage_bijective (hf : Bijective f) : Bijective (t.restrictPreimage f) :=
  ⟨t.restrictPreimage_injective hf.1, t.restrictPreimage_surjective hf.2⟩

alias _root_.Function.Injective.restrictPreimage := Set.restrictPreimage_injective
alias _root_.Function.Surjective.restrictPreimage := Set.restrictPreimage_surjective
alias _root_.Function.Bijective.restrictPreimage := Set.restrictPreimage_bijective

end

/-! ### Injectivity on a set -/
section injOn

/--
theorem `injOn_iff_injective` / 定理 `injOn_iff_injective`

English:
theorem injOn_iff_injective
  statement: InjOn f s ↔ Injective (s.domRestrict f)
  proof: ⟨fun H a b h => Subtype.ext H a.2 b.2 h, fun H a as b bs h =>
congr_arg Subtype.val @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

alias ⟨InjOn.injective, _⟩ := Set.injOn_iff_injective

中文:
定理 injOn_iff_injective
  结论: 单射限制 f s ↔ 单射 (s.domRestrict f)
  证明: ⟨fun H a b h => Subtype.ext H a.2 b.2 h, fun H a as b bs h =>
congr_arg Subtype.val @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

alias ⟨InjOn.injective, _⟩ := Set.injOn_iff_injective

Depends on / 依赖: FreeGroupBasis, FreeGroupBasis.coprodI, IsFreeGroup, IsFreeGroup.basis, Subtype, Subtype.ext, Subtype.val, congr_arg, coprodI, isFreeGroup
-/
theorem injOn_iff_injective : InjOn f s ↔ Injective (s.domRestrict f) :=
⟨fun H a b h => Subtype.ext H a.2 b.2 h, fun H a as b bs h =>
congr_arg Subtype.val @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

alias ⟨InjOn.injective, _⟩ := Set.injOn_iff_injective

set_option backward.isDefEq.respectTransparency false in
/--
theorem `MapsTo.restrict_inj` / 定理 `MapsTo.restrict_inj`

English:
theorem MapsTo.restrict_inj
  given: (h : MapsTo f s t)
  statement: Injective (h.restrict f s t) ↔ InjOn f s
  proof: by
  rw [h.restrict_eq_codRestrict]; rw [injective_codRestrict]; rw [injOn_iff_injective]

中文:
定理 映射到.restrict_inj
  条件: (h : 映射到 f s t)
  结论: 单射 (h.restrict f s t) ↔ 单射限制 f s
  证明: by
  rw [h.restrict_eq_codRestrict]; rw [injective_codRestrict]; rw [injOn_iff_injective]

Depends on / 依赖: h.restrict_eq_codRestrict, injOn_iff_injective, injective_codRestrict, restrict_eq_codRestrict
-/
theorem MapsTo.restrict_inj (h : MapsTo f s t) : Injective (h.restrict f s t) ↔ InjOn f s := by
  rw [h.restrict_eq_codRestrict]; rw [injective_codRestrict]; rw [injOn_iff_injective]

end injOn

/-! ### Surjectivity on a set -/
section surjOn

/--
theorem `surjOn_iff_surjective` / 定理 `surjOn_iff_surjective`

English:
theorem surjOn_iff_surjective
  statement: SurjOn f s univ ↔ Surjective (s.domRestrict f)
  proof: ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivial
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩

@[simp]

中文:
定理 surjOn_iff_surjective
  结论: 满射限制 f s univ ↔ 满射 (s.domRestrict f)
  证明: ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivial
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩

@[simp]
-/
theorem surjOn_iff_surjective : SurjOn f s univ ↔ Surjective (s.domRestrict f) :=
  ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivial
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩

@[simp]
/--
theorem `MapsTo.restrict_surjective_iff` / 定理 `MapsTo.restrict_surjective_iff`

English:
theorem MapsTo.restrict_surjective_iff
  given: (h : MapsTo f s t)
  proof: by
  refine ⟨fun h' b hb => ?_, fun h' ⟨b, hb⟩ => ?_⟩
  · obtain ⟨⟨a, ha⟩, ha'⟩ := h' ⟨b, hb⟩
    replace ha' : f a = b := by simpa [Subtype.ext_iff] using ha'
    rw [← ha']
    exact mem_image_of_mem f ha
  · obtain ⟨a, ha, rfl⟩ := h' hb
    exact ⟨⟨a, ha⟩, rfl⟩

中文:
定理 映射到.restrict_surjective_iff
  条件: (h : 映射到 f s t)
  证明: by
  refine ⟨fun h' b hb => ?_, fun h' ⟨b, hb⟩ => ?_⟩
  · obtain ⟨⟨a, ha⟩, ha'⟩ := h' ⟨b, hb⟩
    replace ha' : f a = b := by simpa [Subtype.ext_iff] using ha'
    rw [← ha']
    exact mem_image_of_mem f ha
  · obtain ⟨a, ha, rfl⟩ := h' hb
    exact ⟨⟨a, ha⟩, rfl⟩

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, mem_image_of_mem, replace
-/
theorem MapsTo.restrict_surjective_iff (h : MapsTo f s t) :
    Surjective (MapsTo.restrict _ _ _ h) ↔ SurjOn f s t := by
  refine ⟨fun h' b hb => ?_, fun h' ⟨b, hb⟩ => ?_⟩
  · obtain ⟨⟨a, ha⟩, ha'⟩ := h' ⟨b, hb⟩
    replace ha' : f a = b := by simpa [Subtype.ext_iff] using ha'
    rw [← ha']
    exact mem_image_of_mem f ha
  · obtain ⟨a, ha, rfl⟩ := h' hb
    exact ⟨⟨a, ha⟩, rfl⟩

end surjOn

end Set
