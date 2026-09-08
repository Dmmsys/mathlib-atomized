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

/-- `α ↪ β` is a bundled injective function. -/
/-
**Function.Embedding** 是 Mathlib 中的一个归纳类型，位于命名空间 `Function`。
形式化陈述：Sort u_1 → Sort u_2 → Sort (max (max 1 u_1) u_2)
参数：max (max 1 u_1) u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α ↪ β` is a bundled injective function.
-/
structure Embedding (α : Sort*) (β : Sort*) where
  /-- An embedding as a function. Use coercion instead. -/
  toFun : α → β
  /-- An embedding is an injective function. Use `Function.Embedding.injective` instead. -/
  inj' : Injective toFun

/-- An embedding, a.k.a. a bundled injective function. -/
infixr:25 " ↪ " => Embedding

/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Sort u} {β : Sort v} : FunLike (α ↪ β) α β where
  coe := Embedding.toFun
  coe_injective f g h := by { cases f; cases g; congr }
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Sort u} {β : Sort v} : EmbeddingLike (α ↪ β) α β where
  injective' := Embedding.inj'

initialize_simps_projections Embedding (toFun → apply)
/-
**Function.** 是 Mathlib 中的一个实例，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Sort*} : CanLift (α → β) (α ↪ β) (↑) Injective where prf f hf := ⟨⟨f, hf⟩, rfl⟩
/-
**Function.exists_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：exists_surjective_iff {α β : Sort*} : (exists f : α -> β, Surjective f) ↔ 
Nonempty (α -> β) ∧ Nonempty (β ↪ α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonempty_fun`：nonempty_fun : Nonempty (α -> β) ↔ IsEmpty α ∨ Nonempty β
· 使用定理 `Function.invFun_surjective`：invFun_surjective (hf : Injective f) : Surje
ctive (invFun f)
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem exists_surjective_iff {α β : Sort*} :
    (∃ f : α → β, Surjective f) ↔ Nonempty (α → β) ∧ Nonempty (β ↪ α) :=
  ⟨fun ⟨f, h⟩ ↦ ⟨⟨f⟩, ⟨⟨_, injective_surjInv h⟩⟩⟩, fun ⟨h, ⟨e⟩⟩ ↦ (nonempty_fun.mp h).elim
    (fun _ ↦ ⟨isEmptyElim, (isEmptyElim <| e ·)⟩) fun _ ↦ ⟨_, invFun_surjective e.inj'⟩⟩

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
/-
**Equiv.toEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Sort u} → {β : Sort v} → α ≃ β → α ↪ β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Convert an `α ≃ β` to `α ↪ β`.

This is also available as a coercion `Equiv.coeEmbedding`.
The explicit `Equiv.toEmbedding` version is preferred though, since the coercion
 can have issues
inferring the type of the resulting embedding. For example:

```lean
-- Works:
example (s : Finset (Fin 3)) (f : Equiv.Perm (Fin 3)) : s.map f.toEmbedding = s.
map f := by simp
-- Error, `f` has type `Fin 3 ≃ Fin 3` but is expected to have type `Fin 3 ↪ ?m_
1 : Type ?`
example (s : Finset (Fin 3)) (f : Equiv.Perm (Fin 3)) : s.map f = s.map f.toEmbe
dding := by simp
```
-/
protected def toEmbedding : α ↪ β :=
  ⟨f, f.injective⟩

@[simp]
/-
**Equiv.coe_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_toEmbedding : (f.toEmbedding : α -> β) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEmbedding : (f.toEmbedding : α → β) = f :=
  rfl
/-
**Equiv.toEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toEmbedding_apply (a : α) : f.toEmbedding a = f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEmbedding_apply (a : α) : f.toEmbedding a = f a :=
  rfl
/-
**Equiv.toEmbedding_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toEmbedding_injective : Function.Injective (Equiv.toEmbedding : (α ≃ β) ->
 (α ↪ β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
-/
theorem toEmbedding_injective : Function.Injective (Equiv.toEmbedding : (α ≃ β) → (α ↪ β)) :=
  fun _ _ h ↦ by rwa [DFunLike.ext'_iff] at h ⊢
/-
**Equiv.coeEmbedding** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
形式化陈述：coeEmbedding : Coe (α ≃ β) (α ↪ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeEmbedding : Coe (α ≃ β) (α ↪ β) :=
  ⟨Equiv.toEmbedding⟩

end Equiv

namespace Function

namespace Embedding

/-
**Function.Embedding.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding
`。
形式化陈述：coe_injective {α β} : @Injective (α ↪ β) (α -> β) (fun f => ↑f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective {α β} : @Injective (α ↪ β) (α → β) (fun f ↦ ↑f) :=
  DFunLike.coe_injective

@[ext]
/-
**Function.Embedding.ext** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：ext {α β} {f g : Embedding α β} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {α β} {f g : Embedding α β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
/-
**Function.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `Function.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Sort*} [IsEmpty α] : Unique (α ↪ β) where
  default := ⟨isEmptyElim, Function.injective_of_subsingleton _⟩
  uniq := by intro; ext v; exact isEmptyElim v

@[simp]
/-
**Function.Embedding.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`
。
形式化陈述：toFun_eq_coe {α β} (f : α ↪ β) : toFun f = f
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {α β} (f : α ↪ β) : toFun f = f :=
  rfl

@[simp]
/-
**Function.Embedding.coeFn_mk** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ f i : α -> β) = f
参数：f : α -> β；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_mk {α β} (f : α → β) (i) : (@mk _ _ f i : α → β) = f :=
  rfl

@[simp]
/-
**Function.Embedding.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：mk_coe {α β : Type*} (f : α ↪ β) (inj) : (⟨f, inj⟩ : α ↪ β) = f
参数：f : α ↪ β；inj。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe {α β : Type*} (f : α ↪ β) (inj) : (⟨f, inj⟩ : α ↪ β) = f :=
  rfl

@[grind! .] -- This adds `Injective f` into the grind context for every embedding `f : α ↪ β`.
/-
**Function.Embedding.injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β), Function.Injective ⇑f
参数：f : α ↪ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
-/
protected theorem injective {α β} (f : α ↪ β) : Injective f :=
  EmbeddingLike.injective f
/-
**Function.Embedding.apply_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embeddi
ng`。
形式化陈述：apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y
参数：f : α ↪ β；x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
-/
theorem apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f

/-- The identity map as a `Function.Embedding`. -/
@[refl, simps +simpRhs]
/-
**Function.Embedding.refl** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：(α : Sort u_1) → α ↪ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id

--- 原说明 ---
The identity map as a `Function.Embedding`.
-/
protected def refl (α : Sort*) : α ↪ α :=
  ⟨id, injective_id⟩

@[norm_cast]
/-
**Function.Embedding.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：coe_refl (α : Sort*) : ⇑(Embedding.refl α) = id
参数：α : Sort*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl (α : Sort*) : ⇑(Embedding.refl α) = id := rfl

/-- Composition of `f : α ↪ β` and `g : β ↪ γ`. -/
@[trans, simps +simpRhs]
/-
**Function.Embedding.trans** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：{α : Sort u_1} → {β : Sort u_2} → {γ : Sort u_3} → (α ↪ β) → (β ↪ γ) → α ↪
 γ
参数：α ↪ β；β ↪ γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `f : α ↪ β` and `g : β ↪ γ`.
-/
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
  ⟨g ∘ f, g.injective.comp f.injective⟩

@[norm_cast]
/-
**Function.Embedding.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：coe_trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : ⇑(f.trans g) = ⇑g ∘ ⇑f
参数：f : α ↪ β；g : β ↪ γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : ⇑(f.trans g) = ⇑g ∘ ⇑f := rfl

@[simp]
/-
**Function.Embedding.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：refl_trans {α β : Type*} (f : α ↪ β) : .trans (.refl α) f = f
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_trans {α β : Type*} (f : α ↪ β) : .trans (.refl α) f = f :=
  rfl

@[simp]
/-
**Function.Embedding.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：trans_refl {α β : Type*} (f : α ↪ β) : .trans f (.refl β) = f
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_refl {α β : Type*} (f : α ↪ β) : .trans f (.refl β) = f :=
  rfl
/-
**Function.Embedding.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：trans_assoc {α β γ δ : Type*} (f : α ↪ β) (g : β ↪ γ) (h : γ ↪ δ) : (f.tra
ns g).trans h = f.trans (g.trans h)
参数：f : α ↪ β；g : β ↪ γ；h : γ ↪ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_assoc {α β γ δ : Type*} (f : α ↪ β) (g : β ↪ γ) (h : γ ↪ δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  rfl
/-
**Function.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `Function.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans Embedding Embedding Embedding := ⟨Embedding.trans⟩
/-
**Function.Embedding.mk_id** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：∀ {α : Sort u_1}, { toFun := id, inj' := ⋯ } = Function.Embedding.refl α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
@[simp] lemma mk_id {α} : mk id injective_id = .refl α := rfl
/-
**Function.Embedding.mk_trans_mk** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β) (g : β → γ) (hf
 : Function.Injective f)   (hg : Function.Injective g),   { toFun := f, inj' := 
hf }.trans { toFun := g, inj' := hg } = { toFun := g ∘ f, inj' := ⋯ }
参数：f : α → β；g : β → γ；hf : Function.Injective f；hg : Function.Injective g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_trans_mk {α β γ} (f : α → β) (g : β → γ) (hf hg) :
    (mk f hf).trans (mk g hg) = mk (g ∘ f) (hg.comp hf) := rfl
/-
**Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding** 是 Mathlib 中的一个定理
，位于命名空间 `Function.Embedding`。
形式化陈述：equiv_toEmbedding_trans_symm_toEmbedding {α β : Sort*} (e : α ≃ β) : e.toE
mbedding.trans e.symm.toEmbedding = Embedding.refl _
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_toEmbedding_trans_symm_toEmbedding {α β : Sort*} (e : α ≃ β) :
    e.toEmbedding.trans e.symm.toEmbedding = Embedding.refl _ := by
  simp
/-
**Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding** 是 Mathlib 中的一个定理
，位于命名空间 `Function.Embedding`。
形式化陈述：equiv_symm_toEmbedding_trans_toEmbedding {α β : Sort*} (e : α ≃ β) : e.sym
m.toEmbedding.trans e.toEmbedding = Embedding.refl _
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_symm_toEmbedding_trans_toEmbedding {α β : Sort*} (e : α ≃ β) :
    e.symm.toEmbedding.trans e.toEmbedding = Embedding.refl _ := by
  simp

/-- Transfer an embedding along a pair of equivalences. -/
@[simps! -fullyApplied +simpRhs]
/-
**Function.Embedding.congr** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：{α : Sort u} → {β : Sort v} → {γ : Sort w} → {δ : Sort x} → α ≃ β → γ ≃ δ 
→ (α ↪ γ) → β ↪ δ
参数：α ↪ γ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer an embedding along a pair of equivalences.
-/
protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
    (f : α ↪ γ) : β ↪ δ :=
  (Equiv.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)

/-- A right inverse `surjInv` of a surjective function as an `Embedding`. -/
/-
**Function.Embedding.ofSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`
。
形式化陈述：{α : Sort u_1} → {β : Sort u_2} → (f : β → α) → Function.Surjective f → α 
↪ β
参数：f : β → α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)

--- 原说明 ---
A right inverse `surjInv` of a surjective function as an `Embedding`.
-/
protected noncomputable def ofSurjective {α β} (f : β → α) (hf : Surjective f) : α ↪ β :=
  ⟨surjInv hf, injective_surjInv _⟩

/-- Convert a surjective `Embedding` to an `Equiv` -/
/-
**Function.Embedding.equivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embed
ding`。
形式化陈述：{α : Sort u_1} → {β : Sort u_2} → (f : α ↪ β) → Function.Surjective ⇑f → α
 ≃ β
参数：f : α ↪ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a surjective `Embedding` to an `Equiv`
-/
protected noncomputable def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f) : α ≃ β :=
  Equiv.ofBijective f ⟨f.injective, hf⟩

/-- Surjective embeddings are equivalent to equivalences. -/
@[simps]
/-
**Function.Embedding._root_.Equiv.embeddingSurjectiveEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `Function.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Surjective embeddings are equivalent to equivalences.
-/
noncomputable def _root_.Equiv.embeddingSurjectiveEquiv {α β} :
    { f : α ↪ β // Surjective f } ≃ (α ≃ β) where
  toFun f := f.val.equivOfSurjective f.prop
  invFun f := ⟨f, f.surjective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

/-- There is always an embedding from an empty type. -/
/-
**Function.Embedding.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：{α : Sort u_1} → {β : Sort u_2} → [IsEmpty α] → α ↪ β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is always an embedding from an empty type.
-/
protected def ofIsEmpty {α β} [IsEmpty α] : α ↪ β :=
  ⟨isEmptyElim, isEmptyElim⟩

/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
/-
**Function.Embedding.setValue** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：setValue {α β : Sort*} (f : α ↪ β) (a : α) (b : β) [forall a', Decidable (
a' = a)] [forall a', Decidable (f a' = b)] : α ↪ β
参数：f : α ↪ β；a : α；b : β；a' = a；f a' = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points.
-/
def setValue {α β : Sort*} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y h
    grind⟩

@[simp]
/-
**Function.Embedding.setValue_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：setValue_eq {α β} (f : α ↪ β) (a : α) (b : β) [forall a', Decidable (a' = 
a)] [forall a', Decidable (f a' = b)] : setValue f a b a = b
参数：f : α ↪ β；a : α；b : β；a' = a；f a' = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setValue_eq {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : setValue f a b a = b := by
  simp [setValue]

@[simp]
/-
**Function.Embedding.setValue_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embeddi
ng`。
形式化陈述：setValue_eq_iff {α β} (f : α ↪ β) {a a' : α} {b : β} [forall a', Decidable
 (a' = a)] [forall a', Decidable (f a' = b)] : setValue f a b a' = b ↔ a' = a
参数：f : α ↪ β；a' = a；f a' = b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Function.Embedding.setValue_eq`：setValue_eq {α β} (f : α ↪ β) (a : α) (b
 : β) [forall a', Decidable (a' = a)] [forall a', Decidable (f a' = b)] : setVal
ue f a b a = b
-/
theorem setValue_eq_iff {α β} (f : α ↪ β) {a a' : α} {b : β} [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] : setValue f a b a' = b ↔ a' = a :=
  (setValue f a b).injective.eq_iff' <| setValue_eq ..
/-
**Function.Embedding.setValue_eq_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Function.Embed
ding`。
形式化陈述：setValue_eq_of_ne {α β} {f : α ↪ β} {a : α} {b : β} {c : α} [forall a', De
cidable (a' = a)] [forall a', Decidable (f a' = b)] (hc : c != a) (hb : f c != b
) : setValue f a b c = f c
参数：a' = a；f a' = b；hc : c != a；hb : f c != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setValue_eq_of_ne {α β} {f : α ↪ β} {a : α} {b : β} {c : α} [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = b)] (hc : c ≠ a) (hb : f c ≠ b) : setValue f a b c = f c := by
  simp [setValue, hc, hb]

@[simp]
/-
**Function.Embedding.setValue_right_apply_eq** 是 Mathlib 中的一个引理，位于命名空间 `Function
.Embedding`。
形式化陈述：setValue_right_apply_eq {α β} (f : α ↪ β) (a c : α) [forall a', Decidable 
(a' = a)] [forall a', Decidable (f a' = f c)] : setValue f a (f c) c = f a
参数：f : α ↪ β；a c : α；a' = a；f a' = f c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
-/
lemma setValue_right_apply_eq {α β} (f : α ↪ β) (a c : α) [∀ a', Decidable (a' = a)]
    [∀ a', Decidable (f a' = f c)] : setValue f a (f c) c = f a := by
  simp [setValue]

/-- Embedding into `Option α` using `some`. -/
@[simps -fullyApplied]
/-
**Function.Embedding.some** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：{α : Type u_1} → α ↪ Option α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)

--- 原说明 ---
Embedding into `Option α` using `some`.
-/
protected def some {α} : α ↪ Option α :=
  ⟨some, Option.some_injective α⟩

/-- A version of `Option.map` for `Function.Embedding`s. -/
@[simps -fullyApplied]
/-
**Function.Embedding.optionMap** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：optionMap {α β} (f : α ↪ β) : Option α ↪ Option β
参数：f : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Option.map` for `Function.Embedding`s.
-/
def optionMap {α β} (f : α ↪ β) : Option α ↪ Option β :=
  ⟨Option.map f, Option.map_injective f.injective⟩

/-- Embedding of a `Subtype`. -/
/-
**Function.Embedding.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：subtype {α} (p : α -> Prop) : Subtype p ↪ α
参数：p : α -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2

--- 原说明 ---
Embedding of a `Subtype`.
-/
def subtype {α} (p : α → Prop) : Subtype p ↪ α :=
  ⟨Subtype.val, fun _ _ => Subtype.ext⟩

@[simp]
/-
**Function.Embedding.subtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding
`。
形式化陈述：subtype_apply {α} {p : α -> Prop} (x : Subtype p) : subtype p x = x
参数：x : Subtype p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply {α} {p : α → Prop} (x : Subtype p) : subtype p x = x :=
  rfl
/-
**Function.Embedding.subtype_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embed
ding`。
形式化陈述：subtype_injective {α} (p : α -> Prop) : Function.Injective (subtype p)
参数：p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem subtype_injective {α} (p : α → Prop) : Function.Injective (subtype p) :=
  Subtype.coe_injective

@[simp]
/-
**Function.Embedding.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：coe_subtype {α} (p : α -> Prop) : ↑(subtype p) = Subtype.val
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype {α} (p : α → Prop) : ↑(subtype p) = Subtype.val :=
  rfl

/-- `Quotient.out` as an embedding. -/
/-
**Function.Embedding.quotientOut** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：quotientOut (α) [s : Setoid α] : Quotient s ↪ α
参数：α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_injective`：Quotient.out_injective {s : Setoid α} : Function
.Injective (@Quotient.out α s)

--- 原说明 ---
`Quotient.out` as an embedding.
-/
noncomputable def quotientOut (α) [s : Setoid α] : Quotient s ↪ α :=
  ⟨_, Quotient.out_injective⟩

@[simp]
/-
**Function.Embedding.coe_quotientOut** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embeddi
ng`。
形式化陈述：coe_quotientOut (α) [Setoid α] : ↑(quotientOut α) = Quotient.out
参数：α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotientOut (α) [Setoid α] : ↑(quotientOut α) = Quotient.out :=
  rfl

/-- Choosing an element `b : β` gives an embedding of `PUnit` into `β`. -/
/-
**Function.Embedding.punit** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：punit {β : Sort*} (b : β) : PUnit ↪ β
参数：b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choosing an element `b : β` gives an embedding of `PUnit` into `β`.
-/
def punit {β : Sort*} (b : β) : PUnit ↪ β :=
  ⟨fun _ => b, by
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩

/-- The equivalence `one ↪ α` with `α`, for `Unique one`. -/
/-
**Function.Embedding.oneEmbeddingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embed
ding`。
形式化陈述：oneEmbeddingEquiv {one α : Type*} [Unique one] : (one ↪ α) ≃ α where toFun
 f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `one ↪ α` with `α`, for `Unique one`.
-/
def oneEmbeddingEquiv {one α : Type*} [Unique one] : (one ↪ α) ≃ α where
  toFun f := f default
  invFun a := {
    toFun := fun _ ↦ a
    inj' x y h := by simp [Unique.uniq inferInstance] }
  left_inv f := by ext; simp [Unique.uniq]

/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
@[simps]
/-
**Function.Embedding.sectL** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：sectL (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β
参数：α : Sort _；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fixing an element `b : β` gives an embedding `α ↪ α × β`.
-/
def sectL (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β :=
  ⟨fun a => (a, b), fun _ _ h => congr_arg Prod.fst h⟩

/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
@[simps]
/-
**Function.Embedding.sectR** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：sectR {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β
参数：a : α；β : Sort _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fixing an element `a : α` gives an embedding `β ↪ α × β`.
-/
def sectR {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β :=
  ⟨fun b => (a, b), fun _ _ h => congr_arg Prod.snd h⟩

/-- If `e₁` and `e₂` are embeddings, then so is `Prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
/-
**Function.Embedding.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ
参数：e₁ : α ↪ β；e₂ : γ ↪ δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e₁` and `e₂` are embeddings, then so is `Prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂
 b)`.
-/
def prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  ⟨Prod.map e₁ e₂, e₁.injective.prodMap e₂.injective⟩

@[simp]
/-
**Function.Embedding.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：coe_prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : e₁.prodMap e₂ = 
Prod.map e₁ e₂
参数：e₁ : α ↪ β；e₂ : γ ↪ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
    e₁.prodMap e₂ = Prod.map e₁ e₂ :=
  rfl

/-- If `e₁` and `e₂` are embeddings,
  then so is `fun ⟨a, b⟩ ↦ ⟨e₁ a, e₂ b⟩ : PProd α γ → PProd β δ`. -/
/-
**Function.Embedding.pprodMap** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：pprodMap {α β γ δ : Sort*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β
 δ
参数：e₁ : α ↪ β；e₂ : γ ↪ δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e₁` and `e₂` are embeddings,
  then so is `fun ⟨a, b⟩ ↦ ⟨e₁ a, e₂ b⟩ : PProd α γ → PProd β δ`.
-/
def pprodMap {α β γ δ : Sort*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β δ :=
  ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.injective.pprod_map e₂.injective⟩

section Sum

open Sum

/-- If `e₁` and `e₂` are embeddings, then so is `Sum.map e₁ e₂`. -/
/-
**Function.Embedding.sumMap** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：sumMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α oplus γ ↪ β oplus δ
参数：e₁ : α ↪ β；e₂ : γ ↪ δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e₁` and `e₂` are embeddings, then so is `Sum.map e₁ e₂`.
-/
def sumMap {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α ⊕ γ ↪ β ⊕ δ :=
  ⟨Sum.map e₁ e₂, e₁.injective.sumMap e₂.injective⟩

@[simp]
/-
**Function.Embedding.coe_sumMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：coe_sumMap {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : sumMap e₁ e₂ = Sum.map e₁
 e₂
参数：e₁ : α ↪ β；e₂ : γ ↪ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sumMap {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : sumMap e₁ e₂ = Sum.map e₁ e₂ :=
  rfl

/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps]
/-
**Function.Embedding.inl** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：inl {α β : Type*} : α ↪ α oplus β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl.inj`：∀ {α : Type u} {β : Type v} {val val_1 : α}, Sum.inl val = 
Sum.inl val_1 → val = val_1

--- 原说明 ---
The embedding of `α` into the sum `α ⊕ β`.
-/
def inl {α β : Type*} : α ↪ α ⊕ β :=
  ⟨Sum.inl, fun _ _ => Sum.inl.inj⟩

/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps]
/-
**Function.Embedding.inr** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：inr {α β : Type*} : β ↪ α oplus β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inr.inj`：∀ {α : Type u} {β : Type v} {val val_1 : β}, Sum.inr val = 
Sum.inr val_1 → val = val_1

--- 原说明 ---
The embedding of `β` into the sum `α ⊕ β`.
-/
def inr {α β : Type*} : β ↪ α ⊕ β :=
  ⟨Sum.inr, fun _ _ => Sum.inr.inj⟩

end Sum

section Sigma

variable {α α' : Type*} {β : α → Type*} {β' : α' → Type*}

/-- `Sigma.mk` as a `Function.Embedding`. -/
@[simps apply]
/-
**Function.Embedding.sigmaMk** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：sigmaMk (a : α) : β a ↪ Σ x, β x
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)

--- 原说明 ---
`Sigma.mk` as a `Function.Embedding`.
-/
def sigmaMk (a : α) : β a ↪ Σ x, β x :=
  ⟨Sigma.mk a, sigma_mk_injective⟩

attribute [grind =] sigmaMk_apply

/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `Sigma.map f g` is an embedding. -/
@[simps apply]
/-
**Function.Embedding.sigmaMap** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：sigmaMap (f : α ↪ α') (g : forall a, β a ↪ β' (f a)) : (Σ a, β a) ↪ Σ a', 
β' a'
参数：f : α ↪ α'；g : forall a, β a ↪ β' (f a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `Sigma.map f g` is an embedding.
-/
def sigmaMap (f : α ↪ α') (g : ∀ a, β a ↪ β' (f a)) : (Σ a, β a) ↪ Σ a', β' a' :=
  ⟨Sigma.map f fun a => g a, f.injective.sigma_map fun a => (g a).injective⟩

end Sigma

/-- Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embeddings
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `fun a ↦ e a (f a)`. -/
@[simps]
/-
**Function.Embedding.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`
。
形式化陈述：piCongrRight {α : Sort*} {β γ : α -> Sort*} (e : forall a, β a ↪ γ a) : (f
orall a, β a) ↪ forall a, γ a
参数：e : forall a, β a ↪ γ a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embedding
s
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `fun a ↦ e a (f a)`.
-/
def piCongrRight {α : Sort*} {β γ : α → Sort*} (e : ∀ a, β a ↪ γ a) : (∀ a, β a) ↪ ∀ a, γ a :=
  ⟨fun f a => e a (f a), fun _ _ h => funext fun a => (e a).injective (congr_fun h a)⟩

/-- An embedding `e : α ↪ β` defines an embedding `(γ → α) ↪ (γ → β)` that sends each `f`
to `e ∘ f`. -/
/-
**Function.Embedding.arrowCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embeddi
ng`。
形式化陈述：arrowCongrRight {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ ->
 α) ↪ γ -> β
参数：e : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding `e : α ↪ β` defines an embedding `(γ → α) ↪ (γ → β)` that sends eac
h `f`
to `e ∘ f`.
-/
def arrowCongrRight {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ → α) ↪ γ → β :=
  piCongrRight fun _ => e

@[simp]
/-
**Function.Embedding.arrowCongrRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.E
mbedding`。
形式化陈述：arrowCongrRight_apply {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (
f : γ -> α) : arrowCongrRight e f = e ∘ f
参数：e : α ↪ β；f : γ -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongrRight_apply {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ → α) :
    arrowCongrRight e f = e ∘ f :=
  rfl

/-- An embedding `e : α ↪ β` defines an embedding `(α → γ) ↪ (β → γ)` for any inhabited type `γ`.
This embedding sends each `f : α → γ` to a function `g : β → γ` such that `g ∘ e = f` and
`g y = default` whenever `y ∉ range e`. -/
/-
**Function.Embedding.arrowCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embeddin
g`。
形式化陈述：arrowCongrLeft {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α
 ↪ β) : (α -> γ) ↪ β -> γ
参数：e : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding `e : α ↪ β` defines an embedding `(α → γ) ↪ (β → γ)` for any inhabi
ted type `γ`.
This embedding sends each `f : α → γ` to a function `g : β → γ` such that `g ∘ e
 = f` and
`g y = default` whenever `y ∉ range e`.
-/
noncomputable def arrowCongrLeft {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) :
    (α → γ) ↪ β → γ :=
  ⟨fun f => extend e f default, fun f₁ f₂ h =>
    funext fun x => by simpa only [e.injective.extend_apply] using congr_fun h (e x)⟩

-- `simps` would generate this over-applied
@[simp]
/-
**Function.Embedding.arrowCongrLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.Em
bedding`。
形式化陈述：arrowCongrLeft_apply {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] 
(e : α ↪ β) (f : α -> γ) : arrowCongrLeft e f = extend e f default
参数：e : α ↪ β；f : α -> γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongrLeft_apply {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β)
    (f : α → γ) :
    arrowCongrLeft e f = extend e f default :=
  rfl

@[simp]
/-
**Function.Embedding.arrowCongrLeft_refl** 是 Mathlib 中的一个定理，位于命名空间 `Function.Emb
edding`。
形式化陈述：arrowCongrLeft_refl {α : Sort u} {γ : Sort w} [Inhabited γ] : (Function.Em
bedding.refl α).arrowCongrLeft (γ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.extend_id`：extend_id (g : α -> γ) (e' : α -> γ) : extend id g e
' = g
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arrowCongrLeft_refl {α : Sort u} {γ : Sort w} [Inhabited γ] :
    (Function.Embedding.refl α).arrowCongrLeft (γ := γ) = .refl _ := by
  ext
  simp [coe_refl]

@[simp]
/-
**Function.Embedding.trans_arrowCongrLeft** 是 Mathlib 中的一个定理，位于命名空间 `Function.Em
bedding`。
形式化陈述：trans_arrowCongrLeft {α₁ : Sort u} {α₂ : Sort v} {α₃ : Sort x} {γ : Sort w
} [Inhabited γ] (e₁₂ : α₁ ↪ α₂) (e₂₃ : α₂ ↪ α₃) : e₁₂.arrowCongrLeft.trans e₂₃.a
rrowCongrLeft = (e₁₂.trans e₂₃).arrowCongrLeft (γ
参数：e₁₂ : α₁ ↪ α₂；e₂₃ : α₂ ↪ α₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Function.Injective.extend_comp`：∀ {γ : Sort u_3} {α₁ : Sort u_4} {α₂ : S
ort u_5} {α₃ : Sort u_6} {f₁₂ : α₁ → α₂},   Function.Injective f₁₂ →     ∀ {f₂₃ 
: α₂ → α₃},       Fu…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem trans_arrowCongrLeft {α₁ : Sort u} {α₂ : Sort v} {α₃ : Sort x} {γ : Sort w}
    [Inhabited γ] (e₁₂ : α₁ ↪ α₂) (e₂₃ : α₂ ↪ α₃) :
    e₁₂.arrowCongrLeft.trans e₂₃.arrowCongrLeft = (e₁₂.trans e₂₃).arrowCongrLeft (γ := γ) := by
  ext f a
  simp only [trans_apply, arrowCongrLeft_apply, Pi.default_def, coe_trans]
  rw [e₁₂.injective.extend_comp e₂₃.injective, Function.comp_def]

/-- Restrict both domain and codomain of an embedding. -/
/-
**Function.Embedding.subtypeMap** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：{α : Sort u_1} →   {β : Sort u_2} →     {p : α → Prop} → {q : β → Prop} → 
(f : α ↪ β) → (∀ ⦃x : α⦄, p x → q (f x)) → { x // p x } ↪ { y // q y }
参数：f : α ↪ β；∀ ⦃x : α⦄, p x → q (f x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict both domain and codomain of an embedding.
-/
protected def subtypeMap {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β)
    (h : ∀ ⦃x⦄, p x → q (f x)) :
    { x : α // p x } ↪ { y : β // q y } :=
  ⟨Subtype.map f h, Subtype.map_injective h f.2⟩

open Set
/-
**Function.Embedding.swap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：swap_apply {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y 
z : α) : Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z)
参数：f : α ↪ β；x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.swap_apply`：Function.Injective.swap_apply [DecidableE
q α] [DecidableEq β] {f : α -> β} (hf : Function.Injective f) (x y z : α) : Equi
v.swap (f x) (f y) …
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem swap_apply {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  f.injective.swap_apply x y z
/-
**Function.Embedding.swap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：swap_comp {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y :
 α) : Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y
参数：f : α ↪ β；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.swap_comp`：Function.Injective.swap_comp [DecidableEq 
α] [DecidableEq β] {f : α -> β} (hf : Function.Injective f) (x y : α) : Equiv.sw
ap (f x) (f y) ∘ f…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
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
/-
**Equiv.asEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：asEmbedding {β α : Sort*} {p : β -> Prop} (e : α ≃ Subtype p) : α ↪ β
参数：e : α ≃ Subtype p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an equivalence to a subtype, produce an embedding to the elements of the c
orresponding
set.
-/
def asEmbedding {β α : Sort*} {p : β → Prop} (e : α ≃ Subtype p) : α ↪ β :=
  e.toEmbedding.trans (subtype p)

/-- The type of embeddings `α ↪ β` is equivalent to
the subtype of all injective functions `α → β`. -/
/-
**Equiv.subtypeInjectiveEquivEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：subtypeInjectiveEquivEmbedding (α β : Sort*) : { f : α -> β // Injective f
 } ≃ (α ↪ β) where toFun f
参数：α β : Sort*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f

--- 原说明 ---
The type of embeddings `α ↪ β` is equivalent to
the subtype of all injective functions `α → β`.
-/
def subtypeInjectiveEquivEmbedding (α β : Sort*) :
    { f : α → β // Injective f } ≃ (α ↪ β) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f, f.injective⟩

/-- If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`. -/
@[simps apply]
/-
**Equiv.embeddingCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：embeddingCongr {α β γ δ : Sort*} (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪
 δ) where toFun f
参数：h : α ≃ β；h' : γ ≃ δ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`.
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
/-
**Equiv.embeddingCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：embeddingCongr_refl {α β : Sort*} : embeddingCongr (Equiv.refl α) (Equiv.r
efl β) = Equiv.refl (α ↪ β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem embeddingCongr_refl {α β : Sort*} :
    embeddingCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α ↪ β) :=
  rfl

@[simp]
/-
**Equiv.embeddingCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：embeddingCongr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*} (e₁ : α₁ ≃ α₂) (e₁' : β₁ 
≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) : embeddingCongr (e₁.trans e₂) (e₁'.trans e
₂') = (embeddingCongr e₁ e₁').trans (embeddingCongr e₂ e₂')
参数：e₁ : α₁ ≃ α₂；e₁' : β₁ ≃ β₂；e₂ : α₂ ≃ α₃；e₂' : β₂ ≃ β₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem embeddingCongr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂)
    (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    embeddingCongr (e₁.trans e₂) (e₁'.trans e₂') =
      (embeddingCongr e₁ e₁').trans (embeddingCongr e₂ e₂') :=
  rfl

@[simp]
/-
**Equiv.embeddingCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：embeddingCongr_symm {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : 
(embeddingCongr e₁ e₂).symm = embeddingCongr e₁.symm e₂.symm
参数：e₁ : α₁ ≃ α₂；e₂ : β₁ ≃ β₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem embeddingCongr_symm {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (embeddingCongr e₁ e₂).symm = embeddingCongr e₁.symm e₂.symm :=
  rfl
/-
**Equiv.embeddingCongr_apply_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：embeddingCongr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb 
: β₁ ≃ β₂) (ec : γ₁ ≃ γ₂) (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) : Equiv.embeddingCongr ea 
ec (f.trans g) = (Equiv.embeddingCongr ea eb f).trans (Equiv.embeddingCongr eb e
c g)
参数：ea : α₁ ≃ α₂；eb : β₁ ≃ β₂；ec : γ₁ ≃ γ₂；f : α₁ ↪ β₁；g : β₁ ↪ γ₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.embeddingCongr_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {δ : Sort u_4} (h : α ≃ β) (h' : γ ≃ δ) (f : α ↪ γ),   (h.embeddingCongr h') 
f = Function.Emb…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.congr_apply`：∀ {α : Sort u} {β : Sort v} {γ : Sort w}
 {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ) (f : α ↪ γ),   ⇑(Function.Embedding.cong
r e₁ e₂ f) = ⇑(f.tra…
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem embeddingCongr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂)
    (ec : γ₁ ≃ γ₂) (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) :
    Equiv.embeddingCongr ea ec (f.trans g) =
      (Equiv.embeddingCongr ea eb f).trans (Equiv.embeddingCongr eb ec g) := by
  ext
  simp

@[simp]
/-
**Equiv.refl_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：refl_toEmbedding {α : Type*} : (Equiv.refl α).toEmbedding = Embedding.refl
 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem refl_toEmbedding {α : Type*} : (Equiv.refl α).toEmbedding = Embedding.refl α :=
  rfl

@[simp]
/-
**Equiv.trans_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：trans_toEmbedding {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) : (e.trans f).to
Embedding = e.toEmbedding.trans f.toEmbedding
参数：e : α ≃ β；f : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem trans_toEmbedding {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
    (e.trans f).toEmbedding = e.toEmbedding.trans f.toEmbedding :=
  rfl

end Equiv

section Subtype

variable {α : Type*}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` can be injectively split
into a sum of subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right. -/
/-
**subtypeOrLeftEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：subtypeOrLeftEmbedding (p q : α -> Prop) [DecidablePred p] : { x // p x ∨ 
q x } ↪ { x // p x } oplus { x // q x }
参数：p q : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` can be injec
tively split
into a sum of subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to th
e right.
-/
def subtypeOrLeftEmbedding (p q : α → Prop) [DecidablePred p] :
    { x // p x ∨ q x } ↪ { x // p x } ⊕ { x // q x } :=
  ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩, by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩

@[simp]
/-
**subtypeOrLeftEmbedding_apply_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subtypeOrLeftEmbedding_apply_left {p q : α -> Prop} [DecidablePred p] (x :
 { x // p x ∨ q x }) (hx : p x) : subtypeOrLeftEmbedding p q x = Sum.inl ⟨x, hx⟩
参数：x : { x // p x ∨ q x }；hx : p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem subtypeOrLeftEmbedding_apply_left {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : p x) :
    subtypeOrLeftEmbedding p q x = Sum.inl ⟨x, hx⟩ :=
  dif_pos hx

@[simp]
/-
**subtypeOrLeftEmbedding_apply_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subtypeOrLeftEmbedding_apply_right {p q : α -> Prop} [DecidablePred p] (x 
: { x // p x ∨ q x }) (hx : ¬p x) : subtypeOrLeftEmbedding p q x = Sum.inr ⟨x, x
.prop.resolve_left hx⟩
参数：x : { x // p x ∨ q x }；hx : ¬p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem subtypeOrLeftEmbedding_apply_right {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) (hx : ¬p x) :
    subtypeOrLeftEmbedding p q x = Sum.inr ⟨x, x.prop.resolve_left hx⟩ :=
  dif_neg hx

@[grind =]
/-
**subtypeOrLeftEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subtypeOrLeftEmbedding_apply {p q : α -> Prop} [DecidablePred p] (x : { x 
// p x ∨ q x }) : subtypeOrLeftEmbedding p q x = if h : p x then Sum.inl ⟨x, h⟩ 
else Sum.inr ⟨x, x.prop.resolve_left h⟩
参数：x : { x // p x ∨ q x }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeOrLeftEmbedding_apply {p q : α → Prop} [DecidablePred p]
    (x : { x // p x ∨ q x }) :
    subtypeOrLeftEmbedding p q x =
      if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩ :=
  rfl

/-- A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`. -/
@[simps (attr := grind =)]
/-
**Subtype.impEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subtype.impEmbedding (p q : α -> Prop) (h : forall x, p x -> q x) : { x //
 p x } ↪ { x // q x }
参数：p q : α -> Prop；h : forall x, p x -> q x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`.
-/
def Subtype.impEmbedding (p q : α → Prop) (h : ∀ x, p x → q x) : { x // p x } ↪ { x // q x } :=
  ⟨fun x => ⟨x, h x x.prop⟩, fun x y => by simp [Subtype.ext_iff]⟩

end Subtype

