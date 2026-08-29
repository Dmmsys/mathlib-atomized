/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Prod.PProd
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Injective functions
-/

@[expose] public section

universe u v w x

namespace Function

/--
Definition of `Embedding` / `Embedding` 的定义

English:
structure Embedding
  parameters: (α : Sort*) (β : Sort*)
  axioms and operations (2):
    - toFun : α -> β
    - inj' : Injective toFun

中文:
结构 Embedding
  参数: (α : Sort*) (β : Sort*)
  公理与运算 (2 个):
    - toFun : α -> β
    - inj' : Injective toFun
-/
structure Embedding (α : Sort*) (β : Sort*) where
  /-- An embedding as a function. Use coercion instead. -/
  toFun : α -> β
  /-- An embedding is an injective function. Use `Function.Embedding.injective` instead. -/
  inj' : Injective toFun

/-- An embedding, a.k.a. a bundled injective function. -/
infixr:25 " ↪ " => Embedding

instance {α : Sort u} {β : Sort v} : FunLike (α ↪ β) α β where
  coe := Embedding.toFun
  coe_injective f g h := by { cases f; cases g; congr }

instance {α : Sort u} {β : Sort v} : EmbeddingLike (α ↪ β) α β where
  injective' := Embedding.inj'

initialize_simps_projections Embedding (toFun -> apply)

instance {α β : Sort*} : CanLift (α -> β) (α ↪ β) (↑) Injective where prf f hf := ⟨⟨f, hf⟩, rfl⟩

/--
theorem `exists_surjective_iff` / 定理 `exists_surjective_iff`

English:
theorem exists_surjective_iff
  given: {α β : Sort*}
  proof: ⟨fun ⟨f, h⟩ => ⟨⟨f⟩, ⟨⟨_, injective_surjInv h⟩⟩⟩, fun ⟨h, ⟨e⟩⟩ => (nonempty_fun.mp h).elim
    (fun _ => ⟨isEmptyElim, (isEmptyElim <| e ·)⟩) fun _ => ⟨_, invFun_surjective e.inj'⟩⟩

中文:
定理 exists_surjective_iff
  条件: {α β : Sort*}
  证明: ⟨fun ⟨f, h⟩ => ⟨⟨f⟩, ⟨⟨_, injective_surjInv h⟩⟩⟩, fun ⟨h, ⟨e⟩⟩ => (nonempty_fun.mp h).elim
    (fun _ => ⟨isEmptyElim, (isEmptyElim <| e ·)⟩) fun _ => ⟨_, invFun_surjective e.inj'⟩⟩

Depends on / 依赖: e.inj, injective_surjInv, invFun_surjective, isEmptyElim, nonempty_fun, nonempty_fun.mp
-/
theorem exists_surjective_iff {α β : Sort*} :
    (exists f : α -> β, Surjective f) ↔ Nonempty (α -> β) ∧ Nonempty (β ↪ α) :=
  ⟨fun ⟨f, h⟩ => ⟨⟨f⟩, ⟨⟨_, injective_surjInv h⟩⟩⟩, fun ⟨h, ⟨e⟩⟩ => (nonempty_fun.mp h).elim
    (fun _ => ⟨isEmptyElim, (isEmptyElim <| e ·)⟩) fun _ => ⟨_, invFun_surjective e.inj'⟩⟩

end Function

namespace Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

/-- Convert an `α ≃ β` to `α ↪ β`.

This is also available as a coercion `Equiv.coeEmbedding`.
The explicit `Equiv.toEmbedding` version is preferred though, since the coercion can have issues
inferring the type of the resulting embedding. For example:

```lean
-- Works:
example (s : Finset (Fin 3)) (f : Equiv.Perm (Fin 3)) : s.map f.toEmbedding = s.map f := by simp
-- Error, `f` has type `Fin 3 ≃ Fin 3` but is expected to have type `Fin 3 ↪ ?m_1 : Type ?`
example (s : Finset (Fin 3)) (f : Equiv.Perm (Fin 3)) : s.map f = s.map f.toEmbedding := by simp
```
-/
@[reducible]
/--
Definition of `toEmbedding` / `toEmbedding` 的定义

English:
definition toEmbedding
  signature: : α ↪ β
  body: ⟨f, f.injective⟩

@[simp]

中文:
定义 toEmbedding
  签名: : α ↪ β
  定义体: ⟨f, f.injective⟩

@[simp]
-/
protected def toEmbedding : α ↪ β :=
  ⟨f, f.injective⟩

@[simp]
/--
theorem `coe_toEmbedding` / 定理 `coe_toEmbedding`

English:
theorem coe_toEmbedding
  statement: (f.toEmbedding : α -> β) = f
  proof: rfl

中文:
定理 coe_toEmbedding
  结论: (f.toEmbedding : α -> β) = f
  证明: rfl
-/
theorem coe_toEmbedding : (f.toEmbedding : α -> β) = f :=
  rfl

/--
theorem `toEmbedding_apply` / 定理 `toEmbedding_apply`

English:
theorem toEmbedding_apply
  given: (a : α)
  statement: f.toEmbedding a = f a
  proof: rfl

中文:
定理 toEmbedding_apply
  条件: (a : α)
  结论: f.toEmbedding a = f a
  证明: rfl
-/
theorem toEmbedding_apply (a : α) : f.toEmbedding a = f a :=
  rfl

/--
theorem `toEmbedding_injective` / 定理 `toEmbedding_injective`

English:
theorem toEmbedding_injective
  statement: Function.Injective (Equiv.toEmbedding : (α ≃ β) -> (α ↪ β))
  proof: fun _ _ h => by rwa [DFunLike.ext'_iff] at h ⊢

中文:
定理 toEmbedding_injective
  结论: Function.Injective (Equiv.toEmbedding : (α ≃ β) -> (α ↪ β))
  证明: fun _ _ h => by rwa [DFunLike.ext'_iff] at h ⊢

Depends on / 依赖: DFunLike, DFunLike.ext, _iff
-/
theorem toEmbedding_injective : Function.Injective (Equiv.toEmbedding : (α ≃ β) -> (α ↪ β)) :=
  fun _ _ h => by rwa [DFunLike.ext'_iff] at h ⊢

/--
Instance `coeEmbedding` / 实例 `coeEmbedding`

English:
instance coeEmbedding
  signature: : Coe (α ≃ β) (α ↪ β)
  body: ⟨Equiv.toEmbedding⟩

中文:
实例 coeEmbedding
  签名: : Coe (α ≃ β) (α ↪ β)
  定义体: ⟨Equiv.toEmbedding⟩

Depends on / 依赖: Equiv.toEmbedding, toEmbedding
-/
instance coeEmbedding : Coe (α ≃ β) (α ↪ β) :=
  ⟨Equiv.toEmbedding⟩

end Equiv

namespace Function

namespace Embedding

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  given: {α β}
  statement: @Injective (α ↪ β) (α -> β) (fun f => ↑f)
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_injective
  条件: {α β}
  结论: @Injective (α ↪ β) (α -> β) (fun f => ↑f)
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective {α β} : @Injective (α ↪ β) (α -> β) (fun f => ↑f) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {α β} {f g : Embedding α β} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {α β} {f g : Embedding α β} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {α β} {f g : Embedding α β} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

instance {α β : Sort*} [IsEmpty α] : Unique (α ↪ β) where
  default := ⟨isEmptyElim, Function.injective_of_subsingleton _⟩
  uniq := by intro; ext v; exact isEmptyElim v

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {α β} (f : α ↪ β)
  statement: toFun f = f
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: {α β} (f : α ↪ β)
  结论: toFun f = f
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe {α β} (f : α ↪ β) : toFun f = f :=
  rfl

@[simp]
/--
theorem `coeFn_mk` / 定理 `coeFn_mk`

English:
theorem coeFn_mk
  given: {α β} (f : α -> β) (i)
  statement: (@mk _ _ f i : α -> β) = f
  proof: rfl

@[simp]

中文:
定理 coeFn_mk
  条件: {α β} (f : α -> β) (i)
  结论: (@mk _ _ f i : α -> β) = f
  证明: rfl

@[simp]
-/
theorem coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ f i : α -> β) = f :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: {α β : Type*} (f : α ↪ β) (inj)
  statement: (⟨f, inj⟩ : α ↪ β) = f
  proof: rfl

@[grind! .] -- This adds `Injective f` into the grind context for every embedding `f : α ↪ β`.

中文:
定理 mk_coe
  条件: {α β : 类型} (f : α ↪ β) (inj)
  结论: (⟨f, inj⟩ : α ↪ β) = f
  证明: rfl

@[grind! .] -- This adds `Injective f` into the grind context for every embedding `f : α ↪ β`.
-/
theorem mk_coe {α β : Type*} (f : α ↪ β) (inj) : (⟨f, inj⟩ : α ↪ β) = f :=
  rfl

@[grind! .] -- This adds `Injective f` into the grind context for every embedding `f : α ↪ β`.
/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: {α β} (f : α ↪ β)
  statement: Injective f
  proof: EmbeddingLike.injective f

中文:
定理 injective
  条件: {α β} (f : α ↪ β)
  结论: Injective f
  证明: EmbeddingLike.injective f
-/
protected theorem injective {α β} (f : α ↪ β) : Injective f :=
  EmbeddingLike.injective f

/--
theorem `apply_eq_iff_eq` / 定理 `apply_eq_iff_eq`

English:
theorem apply_eq_iff_eq
  given: {α β} (f : α ↪ β) (x y : α)
  statement: f x = f y ↔ x = y
  proof: EmbeddingLike.apply_eq_iff_eq f

中文:
定理 apply_eq_iff_eq
  条件: {α β} (f : α ↪ β) (x y : α)
  结论: f x = f y ↔ x = y
  证明: EmbeddingLike.apply_eq_iff_eq f

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, apply_eq_iff_eq
-/
theorem apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f

/-- The identity map as a `Function.Embedding`. -/
@[refl, simps +simpRhs]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (α : Sort*)
  body: ⟨id, injective_id⟩

@[norm_cast]

中文:
定义 refl
  签名: (α : Sort*)
  定义体: ⟨id, injective_id⟩

@[norm_cast]
-/
protected def refl (α : Sort*) : α ↪ α :=
  ⟨id, injective_id⟩

@[norm_cast]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  given: (α : Sort*)
  statement: ⇑(Embedding.refl α) = id
  proof: rfl

中文:
定理 coe_refl
  条件: (α : Sort*)
  结论: ⇑(Embedding.refl α) = id
  证明: rfl
-/
theorem coe_refl (α : Sort*) : ⇑(Embedding.refl α) = id := rfl

/-- Composition of `f : α ↪ β` and `g : β ↪ γ`. -/
@[trans, simps +simpRhs]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {α β γ} (f : α ↪ β) (g : β ↪ γ)
  body: ⟨g ∘ f, g.injective.comp f.injective⟩

@[norm_cast]

中文:
定义 trans
  签名: {α β γ} (f : α ↪ β) (g : β ↪ γ)
  定义体: ⟨g ∘ f, g.injective.comp f.injective⟩

@[norm_cast]
-/
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
  ⟨g ∘ f, g.injective.comp f.injective⟩

@[norm_cast]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: {α β γ} (f : α ↪ β) (g : β ↪ γ)
  statement: ⇑(f.trans g) = ⇑g ∘ ⇑f
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: {α β γ} (f : α ↪ β) (g : β ↪ γ)
  结论: ⇑(f.trans g) = ⇑g ∘ ⇑f
  证明: rfl

@[simp]
-/
theorem coe_trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : ⇑(f.trans g) = ⇑g ∘ ⇑f := rfl

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: {α β : Type*} (f : α ↪ β)
  statement: .trans (.refl α) f = f
  proof: rfl

@[simp]

中文:
定理 refl_trans
  条件: {α β : 类型} (f : α ↪ β)
  结论: .trans (.refl α) f = f
  证明: rfl

@[simp]
-/
theorem refl_trans {α β : Type*} (f : α ↪ β) : .trans (.refl α) f = f :=
  rfl

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: {α β : Type*} (f : α ↪ β)
  statement: .trans f (.refl β) = f
  proof: rfl

中文:
定理 trans_refl
  条件: {α β : 类型} (f : α ↪ β)
  结论: .trans f (.refl β) = f
  证明: rfl
-/
theorem trans_refl {α β : Type*} (f : α ↪ β) : .trans f (.refl β) = f :=
  rfl

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: {α β γ δ : Type*} (f : α ↪ β) (g : β ↪ γ) (h : γ ↪ δ)
  proof: rfl

中文:
定理 trans_assoc
  条件: {α β γ δ : 类型} (f : α ↪ β) (g : β ↪ γ) (h : γ ↪ δ)
  证明: rfl
-/
theorem trans_assoc {α β γ δ : Type*} (f : α ↪ β) (g : β ↪ γ) (h : γ ↪ δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans Embedding Embedding Embedding
  body: ⟨Embedding.trans⟩

中文:
实例 :
  签名: Trans Embedding Embedding Embedding
  定义体: ⟨Embedding.trans⟩

Depends on / 依赖: Embedding, Embedding.trans
-/
instance : Trans Embedding Embedding Embedding := ⟨Embedding.trans⟩

/--
lemma `mk_id` / 引理 `mk_id`

English:
lemma mk_id
  given: {α}
  statement: mk id injective_id = .refl α
  proof: rfl

中文:
引理 mk_id
  条件: {α}
  结论: mk id injective_id = .refl α
  证明: rfl
-/
@[simp] lemma mk_id {α} : mk id injective_id = .refl α := rfl

/--
lemma `mk_trans_mk` / 引理 `mk_trans_mk`

English:
lemma mk_trans_mk
  given: {α β γ} (f : α -> β) (g : β -> γ) (hf hg)
  proof: rfl

中文:
引理 mk_trans_mk
  条件: {α β γ} (f : α -> β) (g : β -> γ) (hf hg)
  证明: rfl
-/
@[simp] lemma mk_trans_mk {α β γ} (f : α -> β) (g : β -> γ) (hf hg) :
    (mk f hf).trans (mk g hg) = mk (g ∘ f) (hg.comp hf) := rfl

/--
theorem `equiv_toEmbedding_trans_symm_toEmbedding` / 定理 `equiv_toEmbedding_trans_symm_toEmbedding`

English:
theorem equiv_toEmbedding_trans_symm_toEmbedding
  given: {α β : Sort*} (e : α ≃ β)
  proof: by
  simp

中文:
定理 equiv_toEmbedding_trans_symm_toEmbedding
  条件: {α β : Sort*} (e : α ≃ β)
  证明: by
  simp
-/
theorem equiv_toEmbedding_trans_symm_toEmbedding {α β : Sort*} (e : α ≃ β) :
    e.toEmbedding.trans e.symm.toEmbedding = Embedding.refl _ := by
  simp

/--
theorem `equiv_symm_toEmbedding_trans_toEmbedding` / 定理 `equiv_symm_toEmbedding_trans_toEmbedding`

English:
theorem equiv_symm_toEmbedding_trans_toEmbedding
  given: {α β : Sort*} (e : α ≃ β)
  proof: by
  simp

中文:
定理 equiv_symm_toEmbedding_trans_toEmbedding
  条件: {α β : Sort*} (e : α ≃ β)
  证明: by
  simp
-/
theorem equiv_symm_toEmbedding_trans_toEmbedding {α β : Sort*} (e : α ≃ β) :
    e.symm.toEmbedding.trans e.toEmbedding = Embedding.refl _ := by
  simp

/-- Transfer an embedding along a pair of equivalences. -/
@[simps! -fullyApplied +simpRhs]
/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
  body: (Equiv.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)

中文:
定义 congr
  签名: {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
  定义体: (Equiv.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)
-/
protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
    (f : α ↪ γ) : β ↪ δ :=
  (Equiv.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def ofSurjective {α β} (f : β -> α) (hf : Surjective f)
  body: ⟨surjInv hf, injective_surjInv _⟩

中文:
定义 noncomputable
  签名: def ofSurjective {α β} (f : β -> α) (hf : Surjective f)
  定义体: ⟨surjInv hf, injective_surjInv _⟩
-/
protected noncomputable def ofSurjective {α β} (f : β -> α) (hf : Surjective f) : α ↪ β :=
  ⟨surjInv hf, injective_surjInv _⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f)
  body: Equiv.ofBijective f ⟨f.injective, hf⟩

中文:
定义 noncomputable
  签名: def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f)
  定义体: Equiv.ofBijective f ⟨f.injective, hf⟩
-/
protected noncomputable def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f) : α ≃ β :=
  Equiv.ofBijective f ⟨f.injective, hf⟩

/-- Surjective embeddings are equivalent to equivalences. -/
@[simps]
/--
Definition of `_root_.Equiv.embeddingSurjectiveEquiv` / `_root_.Equiv.embeddingSurjectiveEquiv` 的定义

English:
definition _root_.Equiv.embeddingSurjectiveEquiv
  signature: {α β}
  body: f.val.equivOfSurjective f.prop
  invFun f := ⟨f, f.surjective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

中文:
定义 _root_.Equiv.embeddingSurjectiveEquiv
  签名: {α β}
  定义体: f.val.equivOfSurjective f.prop
  invFun f := ⟨f, f.surjective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

Depends on / 依赖: equivOfSurjective, f.prop, f.val.equivOfSurjective
-/
noncomputable def _root_.Equiv.embeddingSurjectiveEquiv {α β} :
    { f : α ↪ β // Surjective f } ≃ (α ≃ β) where
  toFun f := f.val.equivOfSurjective f.prop
  invFun f := ⟨f, f.surjective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: {α β} [IsEmpty α]
  body: ⟨isEmptyElim, isEmptyElim⟩

中文:
定义 ofIsEmpty
  签名: {α β} [IsEmpty α]
  定义体: ⟨isEmptyElim, isEmptyElim⟩
-/
protected def ofIsEmpty {α β} [IsEmpty α] : α ↪ β :=
  ⟨isEmptyElim, isEmptyElim⟩

/--
Definition of `setValue` / `setValue` 的定义

English:
definition setValue
  signature: {α β : Sort*} (f : α ↪ β) (a : α) (b : β) [forall a', Decidable (a' = a)]
  body: ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y h
    grind⟩

@[simp]

中文:
定义 setValue
  签名: {α β : Sort*} (f : α ↪ β) (a : α) (b : β) [对任意 a', Decidable (a' = a)]
  定义体: ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y h
    grind⟩

@[simp]
-/
def setValue {α β : Sort*} (f : α ↪ β) (a : α) (b : β) [forall a', Decidable (a' = a)]
    [forall a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y h
    grind⟩

@[simp]
/--
theorem `setValue_eq` / 定理 `setValue_eq`

English:
theorem setValue_eq
  statement: {α β} (f : α ↪ β) (a : α) (b : β) [forall a', Decidable (a' = a)]
  proof: by
  simp [setValue]

@[simp]

中文:
定理 setValue_eq
  结论: {α β} (f : α ↪ β) (a : α) (b : β) [对任意 a', Decidable (a' = a)]
  证明: by
  simp [setValue]

@[simp]

Depends on / 依赖: setValue
-/
theorem setValue_eq {α β} (f : α ↪ β) (a : α) (b : β) [forall a', Decidable (a' = a)]
    [forall a', Decidable (f a' = b)] : setValue f a b a = b := by
  simp [setValue]

@[simp]
/--
theorem `setValue_eq_iff` / 定理 `setValue_eq_iff`

English:
theorem setValue_eq_iff
  statement: {α β} (f : α ↪ β) {a a' : α} {b : β} [forall a', Decidable (a' = a)]
  proof: (setValue f a b).injective.eq_iff' setValue_eq ..

中文:
定理 setValue_eq_iff
  结论: {α β} (f : α ↪ β) {a a' : α} {b : β} [对任意 a', Decidable (a' = a)]
  证明: (setValue f a b).injective.eq_iff' setValue_eq ..

Depends on / 依赖: eq_iff, injective, injective.eq_iff, setValue, setValue_eq
-/
theorem setValue_eq_iff {α β} (f : α ↪ β) {a a' : α} {b : β} [forall a', Decidable (a' = a)]
    [forall a', Decidable (f a' = b)] : setValue f a b a' = b ↔ a' = a :=
(setValue f a b).injective.eq_iff' setValue_eq ..

/--
lemma `setValue_eq_of_ne` / 引理 `setValue_eq_of_ne`

English:
lemma setValue_eq_of_ne
  statement: {α β} {f : α ↪ β} {a : α} {b : β} {c : α} [forall a', Decidable (a' = a)]
  proof: by
  simp [setValue, hc, hb]

@[simp]

中文:
引理 setValue_eq_of_ne
  结论: {α β} {f : α ↪ β} {a : α} {b : β} {c : α} [对任意 a', Decidable (a' = a)]
  证明: by
  simp [setValue, hc, hb]

@[simp]

Depends on / 依赖: setValue
-/
lemma setValue_eq_of_ne {α β} {f : α ↪ β} {a : α} {b : β} {c : α} [forall a', Decidable (a' = a)]
    [forall a', Decidable (f a' = b)] (hc : c != a) (hb : f c != b) : setValue f a b c = f c := by
  simp [setValue, hc, hb]

@[simp]
/--
lemma `setValue_right_apply_eq` / 引理 `setValue_right_apply_eq`

English:
lemma setValue_right_apply_eq
  statement: {α β} (f : α ↪ β) (a c : α) [forall a', Decidable (a' = a)]
  proof: by
  simp [setValue]

中文:
引理 setValue_right_apply_eq
  结论: {α β} (f : α ↪ β) (a c : α) [对任意 a', Decidable (a' = a)]
  证明: by
  simp [setValue]

Depends on / 依赖: setValue
-/
lemma setValue_right_apply_eq {α β} (f : α ↪ β) (a c : α) [forall a', Decidable (a' = a)]
    [forall a', Decidable (f a' = f c)] : setValue f a (f c) c = f a := by
  simp [setValue]

/-- Embedding into `Option α` using `some`. -/
@[simps -fullyApplied]
/--
Definition of `some` / `some` 的定义

English:
definition some
  signature: {α}
  body: ⟨some, Option.some_injective α⟩

中文:
定义 some
  签名: {α}
  定义体: ⟨some, Option.some_injective α⟩
-/
protected def some {α} : α ↪ Option α :=
  ⟨some, Option.some_injective α⟩

/-- A version of `Option.map` for `Function.Embedding`s. -/
@[simps -fullyApplied]
/--
Definition of `optionMap` / `optionMap` 的定义

English:
definition optionMap
  signature: {α β} (f : α ↪ β)
  body: ⟨Option.map f, Option.map_injective f.injective⟩

中文:
定义 optionMap
  签名: {α β} (f : α ↪ β)
  定义体: ⟨Option.map f, Option.map_injective f.injective⟩

Depends on / 依赖: Option.map, Option.map_injective, f.injective, injective, map_injective
-/
def optionMap {α β} (f : α ↪ β) : Option α ↪ Option β :=
  ⟨Option.map f, Option.map_injective f.injective⟩

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: {α} (p : α -> Prop)
  body: ⟨Subtype.val, fun _ _ => Subtype.ext⟩

@[simp]

中文:
定义 subtype
  签名: {α} (p : α -> 命题)
  定义体: ⟨Subtype.val, fun _ _ => Subtype.ext⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, Subtype.val
-/
def subtype {α} (p : α -> Prop) : Subtype p ↪ α :=
  ⟨Subtype.val, fun _ _ => Subtype.ext⟩

@[simp]
/--
theorem `subtype_apply` / 定理 `subtype_apply`

English:
theorem subtype_apply
  given: {α} {p : α -> Prop} (x : Subtype p)
  statement: subtype p x = x
  proof: rfl

中文:
定理 subtype_apply
  条件: {α} {p : α -> 命题} (x : Subtype p)
  结论: subtype p x = x
  证明: rfl
-/
theorem subtype_apply {α} {p : α -> Prop} (x : Subtype p) : subtype p x = x :=
  rfl

/--
theorem `subtype_injective` / 定理 `subtype_injective`

English:
theorem subtype_injective
  given: {α} (p : α -> Prop)
  statement: Function.Injective (subtype p)
  proof: Subtype.coe_injective

@[simp]

中文:
定理 subtype_injective
  条件: {α} (p : α -> 命题)
  结论: Function.Injective (subtype p)
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem subtype_injective {α} (p : α -> Prop) : Function.Injective (subtype p) :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  given: {α} (p : α -> Prop)
  statement: ↑(subtype p) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  条件: {α} (p : α -> 命题)
  结论: ↑(subtype p) = Subtype.val
  证明: rfl
-/
theorem coe_subtype {α} (p : α -> Prop) : ↑(subtype p) = Subtype.val :=
  rfl

/--
Definition of `quotientOut` / `quotientOut` 的定义

English:
definition quotientOut
  signature: (α) [s : Setoid α]
  body: ⟨_, Quotient.out_injective⟩

@[simp]

中文:
定义 quotientOut
  签名: (α) [s : Setoid α]
  定义体: ⟨_, Quotient.out_injective⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.out_injective, out_injective
-/
noncomputable def quotientOut (α) [s : Setoid α] : Quotient s ↪ α :=
  ⟨_, Quotient.out_injective⟩

@[simp]
/--
theorem `coe_quotientOut` / 定理 `coe_quotientOut`

English:
theorem coe_quotientOut
  given: (α) [Setoid α]
  statement: ↑(quotientOut α) = Quotient.out
  proof: rfl

中文:
定理 coe_quotientOut
  条件: (α) [Setoid α]
  结论: ↑(quotientOut α) = Quotient.out
  证明: rfl
-/
theorem coe_quotientOut (α) [Setoid α] : ↑(quotientOut α) = Quotient.out :=
  rfl

/--
Definition of `punit` / `punit` 的定义

English:
definition punit
  signature: {β : Sort*} (b : β)
  body: ⟨fun _ => b, by
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩

中文:
定义 punit
  签名: {β : Sort*} (b : β)
  定义体: ⟨fun _ => b, by
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩
-/
def punit {β : Sort*} (b : β) : PUnit ↪ β :=
  ⟨fun _ => b, by
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩

/--
Definition of `oneEmbeddingEquiv` / `oneEmbeddingEquiv` 的定义

English:
definition oneEmbeddingEquiv
  signature: {one α : Type*} [Unique one]
  body: f default
  invFun a := {
    toFun := fun _ => a
    inj' x y h := by simp [Unique.uniq inferInstance] }
  left_inv f := by ext; simp [Unique.uniq]

中文:
定义 oneEmbeddingEquiv
  签名: {one α : 类型} [Unique one]
  定义体: f default
  invFun a := {
    toFun := fun _ => a
    inj' x y h := by simp [Unique.uniq inferInstance] }
  left_inv f := by ext; simp [Unique.uniq]
-/
def oneEmbeddingEquiv {one α : Type*} [Unique one] : (one ↪ α) ≃ α where
  toFun f := f default
  invFun a := {
    toFun := fun _ => a
    inj' x y h := by simp [Unique.uniq inferInstance] }
  left_inv f := by ext; simp [Unique.uniq]

/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
@[simps]
/--
Definition of `sectL` / `sectL` 的定义

English:
definition sectL
  signature: (α : Sort _) {β : Sort _} (b : β)
  body: ⟨fun a => (a, b), fun _ _ h => congr_arg Prod.fst h⟩

中文:
定义 sectL
  签名: (α : Sort _) {β : Sort _} (b : β)
  定义体: ⟨fun a => (a, b), fun _ _ h => congr_arg Prod.fst h⟩

Depends on / 依赖: Prod.fst, congr_arg
-/
def sectL (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β :=
  ⟨fun a => (a, b), fun _ _ h => congr_arg Prod.fst h⟩

/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
@[simps]
/--
Definition of `sectR` / `sectR` 的定义

English:
definition sectR
  signature: {α : Sort _} (a : α) (β : Sort _)
  body: ⟨fun b => (a, b), fun _ _ h => congr_arg Prod.snd h⟩

中文:
定义 sectR
  签名: {α : Sort _} (a : α) (β : Sort _)
  定义体: ⟨fun b => (a, b), fun _ _ h => congr_arg Prod.snd h⟩

Depends on / 依赖: Prod.snd, congr_arg
-/
def sectR {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β :=
  ⟨fun b => (a, b), fun _ _ h => congr_arg Prod.snd h⟩

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  body: ⟨Prod.map e₁ e₂, e₁.injective.prodMap e₂.injective⟩

@[simp]

中文:
定义 prodMap
  签名: {α β γ δ : 类型} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  定义体: ⟨Prod.map e₁ e₂, e₁.injective.prodMap e₂.injective⟩

@[simp]

Depends on / 依赖: Prod.map, injective, injective.prodMap, prodMap
-/
def prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  ⟨Prod.map e₁ e₂, e₁.injective.prodMap e₂.injective⟩

@[simp]
/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  given: {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  proof: rfl

中文:
定理 coe_prodMap
  条件: {α β γ δ : 类型} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  证明: rfl
-/
theorem coe_prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
    e₁.prodMap e₂ = Prod.map e₁ e₂ :=
  rfl

/--
Definition of `pprodMap` / `pprodMap` 的定义

English:
definition pprodMap
  signature: {α β γ δ : Sort*} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  body: ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.injective.pprod_map e₂.injective⟩

中文:
定义 pprodMap
  签名: {α β γ δ : Sort*} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  定义体: ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.injective.pprod_map e₂.injective⟩

Depends on / 依赖: injective, injective.pprod_map, pprod_map
-/
def pprodMap {α β γ δ : Sort*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β δ :=
  ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.injective.pprod_map e₂.injective⟩

section Sum

open Sum

/--
Definition of `sumMap` / `sumMap` 的定义

English:
definition sumMap
  signature: {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  body: ⟨Sum.map e₁ e₂, e₁.injective.sumMap e₂.injective⟩

@[simp]

中文:
定义 sumMap
  签名: {α β γ δ : 类型} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  定义体: ⟨Sum.map e₁ e₂, e₁.injective.sumMap e₂.injective⟩

@[simp]

Depends on / 依赖: Sum.map, injective, injective.sumMap, sumMap
-/
def sumMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α oplus γ ↪ β oplus δ :=
  ⟨Sum.map e₁ e₂, e₁.injective.sumMap e₂.injective⟩

@[simp]
/--
theorem `coe_sumMap` / 定理 `coe_sumMap`

English:
theorem coe_sumMap
  given: {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  statement: sumMap e₁ e₂ = Sum.map e₁ e₂
  proof: rfl

中文:
定理 coe_sumMap
  条件: {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ)
  结论: sumMap e₁ e₂ = Sum.map e₁ e₂
  证明: rfl
-/
theorem coe_sumMap {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : sumMap e₁ e₂ = Sum.map e₁ e₂ :=
  rfl

/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps]
/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: {α β : Type*}
  body: ⟨Sum.inl, fun _ _ => Sum.inl.inj⟩

中文:
定义 inl
  签名: {α β : 类型}
  定义体: ⟨Sum.inl, fun _ _ => Sum.inl.inj⟩

Depends on / 依赖: Sum.inl, Sum.inl.inj
-/
def inl {α β : Type*} : α ↪ α oplus β :=
  ⟨Sum.inl, fun _ _ => Sum.inl.inj⟩

/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps]
/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: {α β : Type*}
  body: ⟨Sum.inr, fun _ _ => Sum.inr.inj⟩

中文:
定义 inr
  签名: {α β : 类型}
  定义体: ⟨Sum.inr, fun _ _ => Sum.inr.inj⟩

Depends on / 依赖: Sum.inr, Sum.inr.inj
-/
def inr {α β : Type*} : β ↪ α oplus β :=
  ⟨Sum.inr, fun _ _ => Sum.inr.inj⟩

end Sum

section Sigma

variable {α α' : Type*} {β : α -> Type*} {β' : α' -> Type*}

/-- `Sigma.mk` as a `Function.Embedding`. -/
@[simps apply]
/--
Definition of `sigmaMk` / `sigmaMk` 的定义

English:
definition sigmaMk
  signature: (a : α)
  body: ⟨Sigma.mk a, sigma_mk_injective⟩

中文:
定义 sigmaMk
  签名: (a : α)
  定义体: ⟨Sigma.mk a, sigma_mk_injective⟩

Depends on / 依赖: Sigma.mk, sigma_mk_injective
-/
def sigmaMk (a : α) : β a ↪ Σ x, β x :=
  ⟨Sigma.mk a, sigma_mk_injective⟩

attribute [grind =] sigmaMk_apply

/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `Sigma.map f g` is an embedding. -/
@[simps apply]
/--
Definition of `sigmaMap` / `sigmaMap` 的定义

English:
definition sigmaMap
  signature: (f : α ↪ α') (g : forall a, β a ↪ β' (f a))
  body: ⟨Sigma.map f fun a => g a, f.injective.sigma_map fun a => (g a).injective⟩

中文:
定义 sigmaMap
  签名: (f : α ↪ α') (g : 对任意 a, β a ↪ β' (f a))
  定义体: ⟨Sigma.map f fun a => g a, f.injective.sigma_map fun a => (g a).injective⟩

Depends on / 依赖: Sigma.map, f.injective.sigma_map, injective, sigma_map
-/
def sigmaMap (f : α ↪ α') (g : forall a, β a ↪ β' (f a)) : (Σ a, β a) ↪ Σ a', β' a' :=
  ⟨Sigma.map f fun a => g a, f.injective.sigma_map fun a => (g a).injective⟩

end Sigma

/-- Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embeddings
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `fun a ↦ e a (f a)`. -/
@[simps]
/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: {α : Sort*} {β γ : α -> Sort*} (e : forall a, β a ↪ γ a)
  body: ⟨fun f a => e a (f a), fun _ _ h => funext fun a => (e a).injective (congr_fun h a)⟩

中文:
定义 piCongrRight
  签名: {α : Sort*} {β γ : α -> Sort*} (e : 对任意 a, β a ↪ γ a)
  定义体: ⟨fun f a => e a (f a), fun _ _ h => funext fun a => (e a).injective (congr_fun h a)⟩

Depends on / 依赖: congr_fun, injective
-/
def piCongrRight {α : Sort*} {β γ : α -> Sort*} (e : forall a, β a ↪ γ a) : (forall a, β a) ↪ forall a, γ a :=
  ⟨fun f a => e a (f a), fun _ _ h => funext fun a => (e a).injective (congr_fun h a)⟩

/--
Definition of `arrowCongrRight` / `arrowCongrRight` 的定义

English:
definition arrowCongrRight
  signature: {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β)
  body: piCongrRight fun _ => e

@[simp]

中文:
定义 arrowCongrRight
  签名: {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β)
  定义体: piCongrRight fun _ => e

@[simp]

Depends on / 依赖: piCongrRight
-/
def arrowCongrRight {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ -> α) ↪ γ -> β :=
  piCongrRight fun _ => e

@[simp]
/--
theorem `arrowCongrRight_apply` / 定理 `arrowCongrRight_apply`

English:
theorem arrowCongrRight_apply
  given: {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ -> α)
  proof: rfl

中文:
定理 arrowCongrRight_apply
  条件: {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ -> α)
  证明: rfl
-/
theorem arrowCongrRight_apply {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ -> α) :
    arrowCongrRight e f = e ∘ f :=
  rfl

/--
Definition of `arrowCongrLeft` / `arrowCongrLeft` 的定义

English:
definition arrowCongrLeft
  signature: {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β)
  body: ⟨fun f => extend e f default, fun f₁ f₂ h =>
    funext fun x => by simpa only [e.injective.extend_apply] using congr_fun h (e x)⟩

中文:
定义 arrowCongrLeft
  签名: {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β)
  定义体: ⟨fun f => extend e f default, fun f₁ f₂ h =>
    funext fun x => by simpa only [e.injective.extend_apply] using congr_fun h (e x)⟩

Depends on / 依赖: congr_fun, e.injective.extend_apply, extend, extend_apply, injective
-/
noncomputable def arrowCongrLeft {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) :
    (α -> γ) ↪ β -> γ :=
  ⟨fun f => extend e f default, fun f₁ f₂ h =>
    funext fun x => by simpa only [e.injective.extend_apply] using congr_fun h (e x)⟩

-- `simps` would generate this over-applied
@[simp]
/--
theorem `arrowCongrLeft_apply` / 定理 `arrowCongrLeft_apply`

English:
theorem arrowCongrLeft_apply
  statement: {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β)
  proof: rfl

@[simp]

中文:
定理 arrowCongrLeft_apply
  结论: {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β)
  证明: rfl

@[simp]
-/
theorem arrowCongrLeft_apply {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β)
    (f : α -> γ) :
    arrowCongrLeft e f = extend e f default :=
  rfl

@[simp]
/--
theorem `arrowCongrLeft_refl` / 定理 `arrowCongrLeft_refl`

English:
theorem arrowCongrLeft_refl
  given: {α : Sort u} {γ : Sort w} [Inhabited γ]
  proof: by
  ext
  simp [coe_refl]

@[simp]

中文:
定理 arrowCongrLeft_refl
  条件: {α : Sort u} {γ : Sort w} [Inhabited γ]
  证明: by
  ext
  simp [coe_refl]

@[simp]

Depends on / 依赖: coe_refl
-/
theorem arrowCongrLeft_refl {α : Sort u} {γ : Sort w} [Inhabited γ] :
    (Function.Embedding.refl α).arrowCongrLeft (γ := γ) = .refl _ := by
  ext
  simp [coe_refl]

@[simp]
/--
theorem `trans_arrowCongrLeft` / 定理 `trans_arrowCongrLeft`

English:
theorem trans_arrowCongrLeft
  statement: {α₁ : Sort u} {α₂ : Sort v} {α₃ : Sort x} {γ : Sort w}
  proof: by
  ext f a
  simp only [trans_apply, arrowCongrLeft_apply, Pi.default_def, coe_trans]
  rw [e₁₂.injective.extend_comp e₂₃.injective]; rw [Function.comp_def]

中文:
定理 trans_arrowCongrLeft
  结论: {α₁ : Sort u} {α₂ : Sort v} {α₃ : Sort x} {γ : Sort w}
  证明: by
  ext f a
  simp only [trans_apply, arrowCongrLeft_apply, Pi.default_def, coe_trans]
  rw [e₁₂.injective.extend_comp e₂₃.injective]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Pi.default_def, arrowCongrLeft_apply, coe_trans, comp_def, default_def, extend_comp, injective, injective.extend_comp, trans_apply
-/
theorem trans_arrowCongrLeft {α₁ : Sort u} {α₂ : Sort v} {α₃ : Sort x} {γ : Sort w}
    [Inhabited γ] (e₁₂ : α₁ ↪ α₂) (e₂₃ : α₂ ↪ α₃) :
    e₁₂.arrowCongrLeft.trans e₂₃.arrowCongrLeft = (e₁₂.trans e₂₃).arrowCongrLeft (γ := γ) := by
  ext f a
  simp only [trans_apply, arrowCongrLeft_apply, Pi.default_def, coe_trans]
  rw [e₁₂.injective.extend_comp e₂₃.injective]; rw [Function.comp_def]

/--
Definition of `subtypeMap` / `subtypeMap` 的定义

English:
definition subtypeMap
  signature: {α β} {p : α -> Prop} {q : β -> Prop} (f : α ↪ β)
  body: ⟨Subtype.map f h, Subtype.map_injective h f.2⟩

中文:
定义 subtypeMap
  签名: {α β} {p : α -> 命题} {q : β -> 命题} (f : α ↪ β)
  定义体: ⟨Subtype.map f h, Subtype.map_injective h f.2⟩
-/
protected def subtypeMap {α β} {p : α -> Prop} {q : β -> Prop} (f : α ↪ β)
    (h : forall ⦃x⦄, p x -> q (f x)) :
    { x : α // p x } ↪ { y : β // q y } :=
  ⟨Subtype.map f h, Subtype.map_injective h f.2⟩

open Set

/--
theorem `swap_apply` / 定理 `swap_apply`

English:
theorem swap_apply
  given: {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α)
  proof: f.injective.swap_apply x y z

中文:
定理 swap_apply
  条件: {α β : 类型} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α)
  证明: f.injective.swap_apply x y z

Depends on / 依赖: f.injective.swap_apply, injective, swap_apply
-/
theorem swap_apply {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  f.injective.swap_apply x y z

/--
theorem `swap_comp` / 定理 `swap_comp`

English:
theorem swap_comp
  given: {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y : α)
  proof: f.injective.swap_comp x y

中文:
定理 swap_comp
  条件: {α β : 类型} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y : α)
  证明: f.injective.swap_comp x y

Depends on / 依赖: f.injective.swap_comp, injective, swap_comp
-/
theorem swap_comp {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  f.injective.swap_comp x y

end Embedding

end Function

namespace Equiv

open Function Embedding

/-- Given an equivalence to a subtype, produce an embedding to the elements of the corresponding
set. -/
@[simps!]
/--
Definition of `asEmbedding` / `asEmbedding` 的定义

English:
definition asEmbedding
  signature: {β α : Sort*} {p : β -> Prop} (e : α ≃ Subtype p)
  body: e.toEmbedding.trans (subtype p)

中文:
定义 asEmbedding
  签名: {β α : Sort*} {p : β -> 命题} (e : α ≃ Subtype p)
  定义体: e.toEmbedding.trans (subtype p)

Depends on / 依赖: e.toEmbedding.trans, subtype, toEmbedding
-/
def asEmbedding {β α : Sort*} {p : β -> Prop} (e : α ≃ Subtype p) : α ↪ β :=
  e.toEmbedding.trans (subtype p)

/--
Definition of `subtypeInjectiveEquivEmbedding` / `subtypeInjectiveEquivEmbedding` 的定义

English:
definition subtypeInjectiveEquivEmbedding
  signature: (α β : Sort*)
  body: ⟨f.val, f.property⟩
  invFun f := ⟨f, f.injective⟩

中文:
定义 subtypeInjectiveEquivEmbedding
  签名: (α β : Sort*)
  定义体: ⟨f.val, f.property⟩
  invFun f := ⟨f, f.injective⟩

Depends on / 依赖: f.property, f.val, property
-/
def subtypeInjectiveEquivEmbedding (α β : Sort*) :
    { f : α -> β // Injective f } ≃ (α ↪ β) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f, f.injective⟩

/-- If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`. -/
@[simps apply]
/--
Definition of `embeddingCongr` / `embeddingCongr` 的定义

English:
definition embeddingCongr
  signature: {α β γ δ : Sort*} (h : α ≃ β) (h' : γ ≃ δ)
  body: f.congr h h'
  invFun f := f.congr h.symm h'.symm
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

@[simp]

中文:
定义 embeddingCongr
  签名: {α β γ δ : Sort*} (h : α ≃ β) (h' : γ ≃ δ)
  定义体: f.congr h h'
  invFun f := f.congr h.symm h'.symm
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

@[simp]

Depends on / 依赖: f.congr
-/
def embeddingCongr {α β γ δ : Sort*} (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪ δ) where
  toFun f := f.congr h h'
  invFun f := f.congr h.symm h'.symm
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

@[simp]
/--
theorem `embeddingCongr_refl` / 定理 `embeddingCongr_refl`

English:
theorem embeddingCongr_refl
  given: {α β : Sort*}
  proof: rfl

@[simp]

中文:
定理 embeddingCongr_refl
  条件: {α β : Sort*}
  证明: rfl

@[simp]
-/
theorem embeddingCongr_refl {α β : Sort*} :
    embeddingCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α ↪ β) :=
  rfl

@[simp]
/--
theorem `embeddingCongr_trans` / 定理 `embeddingCongr_trans`

English:
theorem embeddingCongr_trans
  statement: {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂)
  proof: rfl

@[simp]

中文:
定理 embeddingCongr_trans
  结论: {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂)
  证明: rfl

@[simp]
-/
theorem embeddingCongr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂)
    (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    embeddingCongr (e₁.trans e₂) (e₁'.trans e₂') =
      (embeddingCongr e₁ e₁').trans (embeddingCongr e₂ e₂') :=
  rfl

@[simp]
/--
theorem `embeddingCongr_symm` / 定理 `embeddingCongr_symm`

English:
theorem embeddingCongr_symm
  given: {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  proof: rfl

中文:
定理 embeddingCongr_symm
  条件: {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
  证明: rfl
-/
theorem embeddingCongr_symm {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (embeddingCongr e₁ e₂).symm = embeddingCongr e₁.symm e₂.symm :=
  rfl

/--
theorem `embeddingCongr_apply_trans` / 定理 `embeddingCongr_apply_trans`

English:
theorem embeddingCongr_apply_trans
  statement: {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  proof: by
  ext
  simp

@[simp]

中文:
定理 embeddingCongr_apply_trans
  结论: {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
  证明: by
  ext
  simp

@[simp]
-/
theorem embeddingCongr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
    (ec : γ₁ ≃ γ₂) (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) :
    Equiv.embeddingCongr ea ec (f.trans g) =
      (Equiv.embeddingCongr ea eb f).trans (Equiv.embeddingCongr eb ec g) := by
  ext
  simp

@[simp]
/--
theorem `refl_toEmbedding` / 定理 `refl_toEmbedding`

English:
theorem refl_toEmbedding
  given: {α : Type*}
  statement: (Equiv.refl α).toEmbedding = Embedding.refl α
  proof: rfl

@[simp]

中文:
定理 refl_toEmbedding
  条件: {α : 类型}
  结论: (Equiv.refl α).toEmbedding = Embedding.refl α
  证明: rfl

@[simp]
-/
theorem refl_toEmbedding {α : Type*} : (Equiv.refl α).toEmbedding = Embedding.refl α :=
  rfl

@[simp]
/--
theorem `trans_toEmbedding` / 定理 `trans_toEmbedding`

English:
theorem trans_toEmbedding
  given: {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ)
  proof: rfl

中文:
定理 trans_toEmbedding
  条件: {α β γ : 类型} (e : α ≃ β) (f : β ≃ γ)
  证明: rfl
-/
theorem trans_toEmbedding {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
    (e.trans f).toEmbedding = e.toEmbedding.trans f.toEmbedding :=
  rfl

end Equiv

section Subtype

variable {α : Type*}

/--
Definition of `subtypeOrLeftEmbedding` / `subtypeOrLeftEmbedding` 的定义

English:
definition subtypeOrLeftEmbedding
  signature: (p q : α -> Prop) [DecidablePred p]
  body: ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩, by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩

@[simp]

中文:
定义 subtypeOrLeftEmbedding
  签名: (p q : α -> 命题) [DecidablePred p]
  定义体: ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩, by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff, Sum.inl, Sum.inr, ext_iff, resolve_left, split_ifs, x.prop.resolve_left
-/
def subtypeOrLeftEmbedding (p q : α -> Prop) [DecidablePred p] :
    { x // p x ∨ q x } ↪ { x // p x } oplus { x // q x } :=
  ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩, by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩

@[simp]
/--
theorem `subtypeOrLeftEmbedding_apply_left` / 定理 `subtypeOrLeftEmbedding_apply_left`

English:
theorem subtypeOrLeftEmbedding_apply_left
  statement: {p q : α -> Prop} [DecidablePred p]
  proof: dif_pos hx

@[simp]

中文:
定理 subtypeOrLeftEmbedding_apply_left
  结论: {p q : α -> 命题} [DecidablePred p]
  证明: dif_pos hx

@[simp]

Depends on / 依赖: dif_pos
-/
theorem subtypeOrLeftEmbedding_apply_left {p q : α -> Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : p x) :
    subtypeOrLeftEmbedding p q x = Sum.inl ⟨x, hx⟩ :=
  dif_pos hx

@[simp]
/--
theorem `subtypeOrLeftEmbedding_apply_right` / 定理 `subtypeOrLeftEmbedding_apply_right`

English:
theorem subtypeOrLeftEmbedding_apply_right
  statement: {p q : α -> Prop} [DecidablePred p]
  proof: dif_neg hx

@[grind =]

中文:
定理 subtypeOrLeftEmbedding_apply_right
  结论: {p q : α -> 命题} [DecidablePred p]
  证明: dif_neg hx

@[grind =]

Depends on / 依赖: dif_neg
-/
theorem subtypeOrLeftEmbedding_apply_right {p q : α -> Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : ¬p x) :
    subtypeOrLeftEmbedding p q x = Sum.inr ⟨x, x.prop.resolve_left hx⟩ :=
  dif_neg hx

@[grind =]
/--
theorem `subtypeOrLeftEmbedding_apply` / 定理 `subtypeOrLeftEmbedding_apply`

English:
theorem subtypeOrLeftEmbedding_apply
  statement: {p q : α -> Prop} [DecidablePred p]
  proof: rfl

中文:
定理 subtypeOrLeftEmbedding_apply
  结论: {p q : α -> 命题} [DecidablePred p]
  证明: rfl
-/
theorem subtypeOrLeftEmbedding_apply {p q : α -> Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) :
    subtypeOrLeftEmbedding p q x =
      if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩ :=
  rfl

/-- A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`. -/
@[simps (attr := grind =)]
/--
Definition of `Subtype.impEmbedding` / `Subtype.impEmbedding` 的定义

English:
definition Subtype.impEmbedding
  signature: (p q : α -> Prop) (h : forall x, p x -> q x)
  body: ⟨fun x => ⟨x, h x x.prop⟩, fun x y => by simp [Subtype.ext_iff]⟩

中文:
定义 Subtype.impEmbedding
  签名: (p q : α -> 命题) (h : 对任意 x, p x -> q x)
  定义体: ⟨fun x => ⟨x, h x x.prop⟩, fun x y => by simp [Subtype.ext_iff]⟩

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, x.prop
-/
def Subtype.impEmbedding (p q : α -> Prop) (h : forall x, p x -> q x) : { x // p x } ↪ { x // q x } :=
  ⟨fun x => ⟨x, h x x.prop⟩, fun x y => by simp [Subtype.ext_iff]⟩

end Subtype
