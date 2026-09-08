/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Multiple transitivity

* `MulAction.IsMultiplyPretransitive`:
  A multiplicative action of a group `G` on a type `α` is n-transitive
  if the action of `G` on `Fin n ↪ α` is pretransitive.

* `MulAction.is_zero_pretransitive` : any action is 0-pretransitive

* `MulAction.is_one_pretransitive_iff` :
  An action is 1-pretransitive iff it is pretransitive

* `MulAction.is_two_pretransitive_iff` :
  An action is 2-pretransitive if for any `a`, `b`, `c`, `d`, such that
  `a ≠ b` and `c ≠ d`, there exist `g : G` such that `g • a = b` and `g • c = d`.

* `MulAction.isPreprimitive_of_is_two_pretransitive` :
  A 2-transitive action is preprimitive

* `MulAction.isMultiplyPretransitive_of_le` :
  If an action is `n`-pretransitive, then it is `m`-pretransitive for all `m ≤ n`,
  provided `α` has at least `n` elements.

## Results for `SubMulAction`.

* `SubMulAction.ofStabilizer.isPretransitive_iff_conj` shows
  that for `a`, `b` and `g` such that `g • a = b`, the actions
  of `stabilizer G a` and of `stabilizer G b` are equivalently `n`-pretransitive for all `n : ℕ`.

* `SubMulAction.ofStabilizer.isMultiplyPretransitive_iff_conj hg` shows the
  same result for `n`-transitivity.


* `SubMulAction.ofStabilizer.isMultiplyPretransitive_iff` : if the action of `G` on `α`
  is pretransitive, then it is `n.succ` pretransitive if and only if
  the action of `stabilizer G a` on `ofStabilizer G a` is `n`-pretransitive.

## Results for permutation groups

* The permutation group is pretransitive, is multiply pretransitive,
  and is preprimitive (for its natural action)

* `Equiv.Perm.eq_top_if_isMultiplyPretransitive`:
  a subgroup of `Equiv.Perm α` which is `Nat.card α - 1` pretransitive is equal to `⊤`.

## Remarks on implementation

These results are results about actions on types `n ↪ α` induced by an action
on `α`, and some results are developed in this context.

-/

@[expose] public section

open MulAction MulActionHom Function.Embedding Fin Set Nat

section Functoriality

variable {G α : Type*} [Group G] [MulAction G α]
variable {H β : Type*} [Group H] [MulAction H β]
variable {σ : G → H} {f : α →ₑ[σ] β} {ι : Type*}

variable (ι) in
/-- An injective equivariant map `α →ₑ[σ] β` induces
an equivariant map on embedding types `(ι ↪ α) → (ι ↪ β)`. -/
@[to_additive /-- An injective equivariant map `α →ₑ[σ] β` induces
an equivariant map on embedding types `(ι ↪ α) → (ι ↪ β)`. -/]
/-
**Function.Injective.mulActionHom_embedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.Injective.mulActionHom_embedding (hf : Function.Injective f) : (ι
 ↪ α) ->ₑ[σ] (ι ↪ β) where toFun x
参数：hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Function.Injective.mulActionHom_embedding (hf : Function.Injective f) :
    (ι ↪ α) →ₑ[σ] (ι ↪ β) where
  toFun x := ⟨f.toFun ∘ x.toFun, hf.comp x.inj'⟩
  map_smul' m x := by ext; simp [f.map_smul']

@[to_additive (attr := simp)]
/-
**Function.Injective.mulActionHom_embedding_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.mulActionHom_embedding_apply (hf : Function.Injective f
) {x : ι ↪ α} {i : ι} : hf.mulActionHom_embedding ι x i = f (x i)
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Function.Injective.mulActionHom_embedding_apply
    (hf : Function.Injective f) {x : ι ↪ α} {i : ι} :
    hf.mulActionHom_embedding ι x i = f (x i) := rfl

@[to_additive]
/-
**Function.Injective.mulActionHom_embedding_isInjective** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Function.Injective.mulActionHom_embedding_isInjective (hf : Function.Injec
tive f) : Function.Injective (hf.mulActionHom_embedding ι)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.mulActionHom_embedding_apply`：Function.Injective.mulA
ctionHom_embedding_apply (hf : Function.Injective f) {x : ι ↪ α} {i : ι} : hf.mu
lActionHom_embedding ι x i = f (x i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Function.Injective.mulActionHom_embedding_isInjective
    (hf : Function.Injective f) :
    Function.Injective (hf.mulActionHom_embedding ι) := by
  intro _ _ hxy
  ext
  apply hf
  simp only [← hf.mulActionHom_embedding_apply, hxy]

variable (hf' : Function.Bijective f)

@[to_additive]
/-
**Function.Bijective.mulActionHom_embedding_isBijective** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Function.Bijective.mulActionHom_embedding_isBijective (hf : Function.Bijec
tive f) : Function.Bijective (hf.injective.mulActionHom_embedding ι)
参数：hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Function.Injective.mulActionHom_embedding_isInjective`：Function.Injectiv
e.mulActionHom_embedding_isInjective (hf : Function.Injective f) : Function.Inje
ctive (hf.mulActionHom_embedding ι)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.mulActionHom_embedding_apply`：Function.Injective.mulA
ctionHom_embedding_apply (hf : Function.Injective f) {x : ι ↪ α} {i : ι} : hf.mu
lActionHom_embedding ι x i = f (x i)
-/
theorem Function.Bijective.mulActionHom_embedding_isBijective (hf : Function.Bijective f) :
    Function.Bijective (hf.injective.mulActionHom_embedding ι) := by
  refine ⟨hf.injective.mulActionHom_embedding_isInjective, ?_⟩
  intro y
  obtain ⟨g, _, hfg⟩ := Function.bijective_iff_has_inverse.mp hf
  use ⟨g ∘ y, hfg.injective.comp (EmbeddingLike.injective y)⟩
  ext
  simp only [hf.injective.mulActionHom_embedding_apply, coeFn_mk, comp_apply]
  exact hfg (y _)

end Functoriality

namespace MulAction

variable {G α : Type*} [Group G] [MulAction G α]

variable (G α) in
/-- An action of a group on a type `α` is `n`-pretransitive
if the associated action on `Fin n ↪ α` is pretransitive. -/
@[to_additive /-- An additive action of an additive group on a type `α`
is `n`-pretransitive if the associated action on `Fin n ↪ α` is pretransitive. -/]
/-
**MulAction.IsMultiplyPretransitive** 是 Mathlib 中的一个缩写定义，位于命名空间 `MulAction`。
形式化陈述：IsMultiplyPretransitive (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev IsMultiplyPretransitive (n : ℕ) := IsPretransitive G (Fin n ↪ α)

@[to_additive]
/-
**MulAction.isMultiplyPretransitive_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：isMultiplyPretransitive_iff {n : Nat} : IsMultiplyPretransitive G α n ↔ fo
rall x y : Fin n ↪ α, exists g : G, g • x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPretransitive_iff`：∀ (M : Type u_5) (α : Type u_6) [inst : S
Mul M α], MulAction.IsPretransitive M α ↔ ∀ (x y : α), ∃ g, g • x = y
-/
theorem isMultiplyPretransitive_iff {n : ℕ} :
    IsMultiplyPretransitive G α n ↔ ∀ x y : Fin n ↪ α, ∃ g : G, g • x = y :=
  isPretransitive_iff _ _

variable {H β : Type*} [Group H] [MulAction H β] {σ : G → H}
  {f : α →ₑ[σ] β} (hf : Function.Injective f)

/-- If there exists a surjective equivariant map `α →ₑ[σ] β`
then pretransitivity descends from `n ↪ α` to `n ↪ β`.

The subtlety is that if it is not injective, this map does not induce
an equivariant map from `n ↪ α` to `n ↪ β`. -/
@[to_additive]
/-
**MulAction.IsPretransitive.of_embedding** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Is
Pretransitive`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{H : Type u_3} {β : Type u_4}   [inst_2 : Group H] [inst_3 : MulAction H β] {σ :
 G → H} {f : α →ₑ[σ] β} {n : Type u_5},   Function.Surjective ⇑f → ∀ [MulAction.
IsPretransitive G (n ↪ α)], MulAction.IsPretransitive H (n ↪ β)
参数：n ↪ α；n ↪ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `Function.Embedding.smul_apply`：smul_apply [Group G] [MulAction G β] (g :
 G) (f : α ↪ β) (a : α) : (g • f) a = g • f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `MulActionHom.map_smul'`：∀ {M : Type u_2} {N : Type u_3} {φ : M → N} {X :
 Type u_5} [inst : SMul M X] {Y : Type u_6} [inst_1 : SMul N Y]   (self : X →ₑ[φ
] Y) (m : M)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If there exists a surjective equivariant map `α →ₑ[σ] β`
then pretransitivity descends from `n ↪ α` to `n ↪ β`.

The subtlety is that if it is not injective, this map does not induce
an equivariant map from `n ↪ α` to `n ↪ β`.
-/
theorem IsPretransitive.of_embedding {n : Type*}
    (hf : Function.Surjective f) [IsPretransitive G (n ↪ α)] :
    IsPretransitive H (n ↪ β) where
  exists_smul_eq x y := by
    let aux (x : n ↪ β) : (n ↪ α) :=
      x.trans (Function.Embedding.ofSurjective (⇑f) hf)
    have aux_apply (x : n ↪ β) (i : n) : f.toFun (aux x i) = x i := by
      simp only [trans_apply, aux]
      apply Function.surjInv_eq
    obtain ⟨g, hg⟩ := exists_smul_eq (M := G) (aux x) (aux y)
    use σ g
    ext i
    rw [DFunLike.ext_iff] at hg
    rw [smul_apply]
    simp [← aux_apply, ← hg, MulActionHom.map_smul']

@[to_additive]
/-
**MulAction.IsPretransitive.of_embedding_congr** 是 Mathlib 中的一个定理，位于命名空间 `MulAct
ion.IsPretransitive`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{H : Type u_3} {β : Type u_4}   [inst_2 : Group H] [inst_3 : MulAction H β] {σ :
 G → H} {f : α →ₑ[σ] β} {n : Type u_5},   Function.Surjective σ →     Function.B
ijective ⇑f → (MulAction.IsPretransitive G (n ↪ α) ↔ MulAction.IsPretransitive H
 (n ↪ β))
参数：MulAction.IsPretransitive G (n ↪ α) ↔ MulAction.IsPretransitive H (n ↪ β)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPretransitive_congr`：isPretransitive_congr {φ : M -> N} {f :
 α ->ₑ[φ] β} (hφ : Function.Surjective φ) (hf : Function.Bijective f) : IsPretra
nsitive M α ↔ IsPretr…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Function.Bijective.mulActionHom_embedding_isBijective`：Function.Bijectiv
e.mulActionHom_embedding_isBijective (hf : Function.Bijective f) : Function.Bije
ctive (hf.injective.mulActionHom_embedding …
-/
theorem IsPretransitive.of_embedding_congr {n : Type*}
    (hσ : Function.Surjective σ) (hf : Function.Bijective f) :
    IsPretransitive G (n ↪ α) ↔ IsPretransitive H (n ↪ β) :=
  isPretransitive_congr hσ hf.mulActionHom_embedding_isBijective

section Zero

/-- Any action is 0-pretransitive. -/
@[to_additive]
/-
**MulAction.is_zero_pretransitive** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：is_zero_pretransitive {n : Type*} [IsEmpty n] : IsPretransitive G (n ↪ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
Any action is 0-pretransitive.
-/
theorem is_zero_pretransitive {n : Type*} [IsEmpty n] :
    IsPretransitive G (n ↪ α) := inferInstance

/-- Any action is 0-pretransitive. -/
@[to_additive]
/-
**MulAction.is_zero_pretransitive'** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：is_zero_pretransitive' : IsMultiplyPretransitive G α 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
Any action is 0-pretransitive.
-/
theorem is_zero_pretransitive' :
    IsMultiplyPretransitive G α 0 := inferInstance

end Zero

section One

variable {one : Type*} [Unique one]

/-- For `Unique one`, the equivariant map from `one ↪ α` to `α`. -/
@[to_additive /-- For `Unique one`, the equivariant map from `one ↪ α` to `α` -/]
/-
**MulAction._root_.MulActionHom.oneEmbeddingMap** 是 Mathlib 中的一个定义，位于命名空间 `MulAc
tion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `Unique one`, the equivariant map from `one ↪ α` to `α`.
-/
def _root_.MulActionHom.oneEmbeddingMap :
    (one ↪ α) →[G] α := {
  oneEmbeddingEquiv with
  map_smul' _ _ := rfl }

@[to_additive]
/-
**MulAction._root_.MulActionHom.oneEmbeddingMap_bijective** 是 Mathlib 中的一个定理，位于命
名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulActionHom.oneEmbeddingMap_bijective :
    Function.Bijective (oneEmbeddingMap (one := one) (G := G) (α := α)) :=
  oneEmbeddingEquiv.bijective

/-- An action is `1`-pretransitive iff it is pretransitive. -/
@[to_additive /-- An additive action is `1`-pretransitive iff it is pretransitive. -/]
/-
**MulAction.oneEmbedding_isPretransitive_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulActio
n`。
形式化陈述：oneEmbedding_isPretransitive_iff : IsPretransitive G (one ↪ α) ↔ IsPretran
sitive G α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPretransitive_congr`：isPretransitive_congr {φ : M -> N} {f :
 α ->ₑ[φ] β} (hφ : Function.Surjective φ) (hf : Function.Bijective f) : IsPretra
nsitive M α ↔ IsPretr…
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `MulActionHom.oneEmbeddingMap_bijective`：∀ {G : Type u_1} {α : Type u_2} 
[inst : Group G] [inst_1 : MulAction G α] {one : Type u_5} [inst_2 : Unique one]
,   Function.Bijective ⇑MulA…

--- 原说明 ---
An action is `1`-pretransitive iff it is pretransitive.
-/
theorem oneEmbedding_isPretransitive_iff :
    IsPretransitive G (one ↪ α) ↔ IsPretransitive G α :=
  isPretransitive_congr Function.surjective_id oneEmbeddingMap_bijective

/-- An action is `1`-pretransitive iff it is pretransitive. -/
@[to_additive /-- An additive action is `1`-pretransitive iff it is pretransitive. -/]
/-
**MulAction.is_one_pretransitive_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：is_one_pretransitive_iff : IsMultiplyPretransitive G α 1 ↔ IsPretransitive
 G α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.oneEmbedding_isPretransitive_iff`：oneEmbedding_isPretransitive
_iff : IsPretransitive G (one ↪ α) ↔ IsPretransitive G α

--- 原说明 ---
An action is `1`-pretransitive iff it is pretransitive.
-/
theorem is_one_pretransitive_iff :
    IsMultiplyPretransitive G α 1 ↔ IsPretransitive G α :=
  oneEmbedding_isPretransitive_iff

end One

section Two

/-- An action is `2`-pretransitive iff
it can move any two distinct elements to any two distinct elements. -/
@[to_additive /-- An additive action is `2`-pretransitive iff
it can move any two distinct elements to any two distinct elements. -/]
/-
**MulAction.is_two_pretransitive_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：is_two_pretransitive_iff : IsMultiplyPretransitive G α 2 ↔ forall {a b c d
 : α} (_ : a != b) (_ : c != d), exists g : G, g • a = c ∧ g • b = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Embedding.embFinTwo_apply_zero`：embFinTwo_apply_zero {a b : α} 
(h : a != b) : embFinTwo h 0 = a
· 使用定理 `Function.Embedding.smul_apply`：smul_apply [Group G] [MulAction G β] (g :
 G) (f : α ↪ β) (a : α) : (g • f) a = g • f a
· 使用定理 `Function.Embedding.embFinTwo_apply_one`：embFinTwo_apply_one {a b : α} (h
 : a != b) : embFinTwo h 1 = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Fin.zero_ne_one`：∀ {n : ℕ}, 0 ≠ 1
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Fin.eq_one_of_ne_zero`：eq_one_of_ne_zero (i : Fin 2) (hi : i != 0) : i =
 1
-/
theorem is_two_pretransitive_iff :
    IsMultiplyPretransitive G α 2 ↔
      ∀ {a b c d : α} (_ : a ≠ b) (_ : c ≠ d), ∃ g : G, g • a = c ∧ g • b = d := by
  constructor
  · intro _ a b c d h h'
    obtain ⟨m, e⟩ := exists_smul_eq (M := G) (embFinTwo h) (embFinTwo h')
    exact ⟨m,
      by rw [← embFinTwo_apply_zero h, ← smul_apply, e, embFinTwo_apply_zero],
      by rw [← embFinTwo_apply_one h, ← smul_apply, e, embFinTwo_apply_one]⟩
  · intro H
    constructor
    intro j j'
    obtain ⟨g, h, h'⟩ :=
      H (j.injective.ne_iff.mpr Fin.zero_ne_one) (j'.injective.ne_iff.mpr Fin.zero_ne_one)
    use g
    ext i
    by_cases hi : i = 0
    · simp [hi, h]
    · simp [eq_one_of_ne_zero i hi, h']

/-- A `2`-pretransitive action is pretransitive. -/
@[to_additive /-- A `2`-pretransitive additive action is pretransitive. -/]
/-
**MulAction.isPretransitive_of_is_two_pretransitive** 是 Mathlib 中的一个定理，位于命名空间 `M
ulAction`。
形式化陈述：isPretransitive_of_is_two_pretransitive [h2 : IsMultiplyPretransitive G α 
2] : IsPretransitive G α where exists_smul_eq a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulAction.is_two_pretransitive_iff`：is_two_pretransitive_iff : IsMultipl
yPretransitive G α 2 ↔ forall {a b c d : α} (_ : a != b) (_ : c != d), exists g 
: G, g • a = c ∧ g • b =…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
A `2`-pretransitive action is pretransitive.
-/
theorem isPretransitive_of_is_two_pretransitive
    [h2 : IsMultiplyPretransitive G α 2] : IsPretransitive G α where
  exists_smul_eq a b := by
    by_cases h : a = b
    · exact ⟨1, by simp [h]⟩
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, h, _⟩ := h2 h (Ne.symm h)
      exact ⟨g, h⟩

/-- A `2`-transitive action is primitive. -/
@[to_additive /-- A `2`-transitive additive action is primitive. -/]
/-
**MulAction.isPreprimitive_of_is_two_pretransitive** 是 Mathlib 中的一个定理，位于命名空间 `Mu
lAction`。
形式化陈述：isPreprimitive_of_is_two_pretransitive (h2 : IsMultiplyPretransitive G α 2
) : IsPreprimitive G α
参数：h2 : IsMultiplyPretransitive G α 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPretransitive_of_is_two_pretransitive`：isPretransitive_of_is
_two_pretransitive [h2 : IsMultiplyPretransitive G α 2] : IsPretransitive G α wh
ere exists_smul_eq a b
· 使用定理 `Set.subsingleton_or_nontrivial`：∀ {α : Type u} (s : Set α), s.Subsinglet
on ∨ s.Nontrivial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.top_eq_univ`：top_eq_univ : (⊤ : Set α) = univ
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `MulAction.is_two_pretransitive_iff`：is_two_pretransitive_iff : IsMultipl
yPretransitive G α 2 ↔ forall {a b c d : α} (_ : a != b) (_ : c != d), exists g 
: G, g • a = c ∧ g • b =…
· 使用引理 `MulAction.isBlock_iff_smul_eq_of_mem`：isBlock_iff_smul_eq_of_mem : IsBlo
ck G B ↔ forall ⦃g : G⦄ ⦃a : X⦄, a in B -> g • a in B -> g • B = B
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s

--- 原说明 ---
A `2`-transitive action is primitive.
-/
theorem isPreprimitive_of_is_two_pretransitive
    (h2 : IsMultiplyPretransitive G α 2) : IsPreprimitive G α := by
  have : IsPretransitive G α := isPretransitive_of_is_two_pretransitive
  apply IsPreprimitive.mk
  intro B hB
  rcases B.subsingleton_or_nontrivial with h | h
  · left
    exact h
  · right
    obtain ⟨a, ha, b, hb, h⟩ := h
    rw [← top_eq_univ, eq_top_iff]
    intro c _
    by_cases h' : a = c
    · rw [← h']; exact ha
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, hga, hgb⟩ := h2 h h'
      rw [MulAction.isBlock_iff_smul_eq_of_mem] at hB
      rw [← hB (g := g) ha (by rw [hga]; exact ha), ← hgb]
      exact smul_mem_smul_set hb

end Two

section Higher

variable (G α) in
/-- The natural equivariant map from `n ↪ α` to `m ↪ α` given by an embedding
`e : m ↪ n`. -/
@[to_additive
/-- The natural equivariant map from `n ↪ α` to `m ↪ α` given by an embedding `e : m ↪ n`. -/]
/-
**MulAction._root_.MulActionHom.embMap** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.MulActionHom.embMap {m n : Type*} (e : m ↪ n) :
    (n ↪ α) →[G] (m ↪ α) where
  toFun i := e.trans i
  map_smul' _ _ := rfl

/-- If `α` has at least `n` elements, then any `n`-pretransitive action on `α`
is `m`-pretransitive for any `m ≤ n`.

This version allows `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `MulAction.isMultiplyPretransitive_of_le` -/
@[to_additive
/-- If `α` has at least `n` elements, then any `n`-pretransitive action on `α`
is `n`-pretransitive for any `m ≤ n`.

This version allows `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `AddAction.isMultiplyPretransitive_of_le`. -/]
/-
**MulAction.isMultiplyPretransitive_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`
。
形式化陈述：isMultiplyPretransitive_of_le' {m n : Nat} [IsMultiplyPretransitive G α n]
 (hmn : m <= n) (hα : n <= ENat.card α) : IsMultiplyPretransitive G α m
参数：hmn : m <= n；hα : n <= ENat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `MulAction.IsPretransitive.of_surjective_map`：∀ {M : Type u_3} {N : Type 
u_4} {α : Type u_5} {β : Type u_6} [inst : Monoid M] [inst_1 : Monoid N]   [inst
_2 : MulAction M α] [inst_3 : Mul…
· 使用定理 `Fin.Embedding.restrictSurjective_of_add_le_ENatCard`：restrictSurjective_
of_add_le_ENatCard (hn : m + n <= ENat.card α) : Surjective (fun (x : Fin (m + n
) ↪ α) => (Fin.castAddEmb n).trans x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isMultiplyPretransitive_of_le' {m n : ℕ} [IsMultiplyPretransitive G α n]
    (hmn : m ≤ n) (hα : n ≤ ENat.card α) :
    IsMultiplyPretransitive G α m := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map
    (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_ENatCard hα) inferInstance

/-- If `α` has at least `n` elements, then an `n`-pretransitive action
is `m`-pretransitive for any `m ≤ n`.

For an infinite `α`, use `MulAction.isMultiplyPretransitive_of_le'`. -/
@[to_additive
/-- If `α` has at least `n` elements, then an `n`-pretransitive action
is `m`-pretransitive for any `m ≤ n`.

For an infinite `α`, use `MulAction.isMultiplyPretransitive_of_le'`. -/]
/-
**MulAction.isMultiplyPretransitive_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：isMultiplyPretransitive_of_le {m n : Nat} [IsMultiplyPretransitive G α n] 
(hmn : m <= n) (hα : n <= Nat.card α) [Finite α] : IsMultiplyPretransitive G α m
参数：hmn : m <= n；hα : n <= Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `MulAction.IsPretransitive.of_surjective_map`：∀ {M : Type u_3} {N : Type 
u_4} {α : Type u_5} {β : Type u_6} [inst : Monoid M] [inst_1 : Monoid N]   [inst
_2 : MulAction M α] [inst_3 : Mul…
· 使用定理 `Fin.Embedding.restrictSurjective_of_add_le_natCard`：restrictSurjective_o
f_add_le_natCard [Finite α] (hn : m + n <= Nat.card α) : Surjective (fun x : Fin
 (m + n) ↪ α => (castAddEmb n).trans x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isMultiplyPretransitive_of_le {m n : ℕ} [IsMultiplyPretransitive G α n]
    (hmn : m ≤ n) (hα : n ≤ Nat.card α) [Finite α] :
    IsMultiplyPretransitive G α m := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_natCard hα) inferInstance

end Higher

end MulAction

namespace SubMulAction.ofStabilizer

variable {G α : Type*} [Group G] [MulAction G α]

@[to_additive]
/-
**SubMulAction.ofStabilizer.isPretransitive_iff_of_conj** 是 Mathlib 中的一个定理，位于命名空
间 `SubMulAction.ofStabilizer`。
形式化陈述：isPretransitive_iff_of_conj {a b : α} {g : G} (hg : b = g • a) : IsPretran
sitive (stabilizer G a) (ofStabilizer G a) ↔ IsPretransitive (stabilizer G b) (o
fStabilizer G b)
参数：hg : b = g • a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPretransitive_congr`：isPretransitive_congr {φ : M -> N} {f :
 α ->ₑ[φ] β} (hφ : Function.Surjective φ) (hf : Function.Bijective f) : IsPretra
nsitive M α ↔ IsPretr…
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `SubMulAction.ofStabilizer.conjMap_bijective`：∀ {G : Type u_1} [inst : Gr
oup G] {α : Type u_2} [inst_1 : MulAction G α] {g : G} {a b : α} (hg : b = g • a
),   Function.Bijective ⇑(SubMulA…
-/
theorem isPretransitive_iff_of_conj {a b : α} {g : G} (hg : b = g • a) :
    IsPretransitive (stabilizer G a) (ofStabilizer G a) ↔
      IsPretransitive (stabilizer G b) (ofStabilizer G b) :=
  isPretransitive_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]
/-
**SubMulAction.ofStabilizer.isPretransitive_iff** 是 Mathlib 中的一个定理，位于命名空间 `SubMu
lAction.ofStabilizer`。
形式化陈述：isPretransitive_iff [IsPretransitive G α] {a b : α} : IsPretransitive (sta
bilizer G a) (ofStabilizer G a) ↔ IsPretransitive (stabilizer G b) (ofStabilizer
 G b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `SubMulAction.ofStabilizer.isPretransitive_iff_of_conj`：isPretransitive_i
ff_of_conj {a b : α} {g : G} (hg : b = g • a) : IsPretransitive (stabilizer G a)
 (ofStabilizer G a) ↔ IsPretransitive (stab…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isPretransitive_iff [IsPretransitive G α] {a b : α} :
    IsPretransitive (stabilizer G a) (ofStabilizer G a) ↔
      IsPretransitive (stabilizer G b) (ofStabilizer G b) :=
  let ⟨_, hg⟩ := exists_smul_eq G a b
  isPretransitive_iff_of_conj hg.symm

@[to_additive]
/-
**SubMulAction.ofStabilizer.isMultiplyPretransitive_iff_of_conj** 是 Mathlib 中的一个
定理，位于命名空间 `SubMulAction.ofStabilizer`。
形式化陈述：isMultiplyPretransitive_iff_of_conj {n : Nat} {a b : α} {g : G} (hg : b = 
g • a) : IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔ IsMulti
plyPretransitive (stabilizer G b) (ofStabilizer G b) n
参数：hg : b = g • a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.of_embedding_congr`：∀ {G : Type u_1} {α : Type
 u_2} [inst : Group G] [inst_1 : MulAction G α] {H : Type u_3} {β : Type u_4}   
[inst_2 : Group H] [inst_3 : MulAc…
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `SubMulAction.ofStabilizer.conjMap_bijective`：∀ {G : Type u_1} [inst : Gr
oup G] {α : Type u_2} [inst_1 : MulAction G α] {g : G} {a b : α} (hg : b = g • a
),   Function.Bijective ⇑(SubMulA…
-/
theorem isMultiplyPretransitive_iff_of_conj
    {n : ℕ} {a b : α} {g : G} (hg : b = g • a) :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n :=
  IsPretransitive.of_embedding_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]
/-
**SubMulAction.ofStabilizer.isMultiplyPretransitive_iff** 是 Mathlib 中的一个定理，位于命名空
间 `SubMulAction.ofStabilizer`。
形式化陈述：isMultiplyPretransitive_iff [IsPretransitive G α] {n : Nat} {a b : α} : Is
MultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔ IsMultiplyPretrans
itive (stabilizer G b) (ofStabilizer G b) n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `SubMulAction.ofStabilizer.isMultiplyPretransitive_iff_of_conj`：isMultipl
yPretransitive_iff_of_conj {n : Nat} {a b : α} {g : G} (hg : b = g • a) : IsMult
iplyPretransitive (stabilizer G a) (ofStabilizer G …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isMultiplyPretransitive_iff [IsPretransitive G α] {n : ℕ} {a b : α} :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n :=
  let ⟨_, hg⟩ := exists_smul_eq G a b
  isMultiplyPretransitive_iff_of_conj hg.symm

/-- Multiple transitivity of a pretransitive action
is equivalent to one less transitivity of stabilizer of a point
(Wielandt, th. 9.1, 1st part) -/
@[to_additive /-- Multiple transitivity of a pretransitive action
is equivalent to one less transitivity of stabilizer of a point
[Wielandt, th. 9.1, 1st part][Wielandt-1964]. -/]
/-
**SubMulAction.ofStabilizer.isMultiplyPretransitive** 是 Mathlib 中的一个定理，位于命名空间 `S
ubMulAction.ofStabilizer`。
形式化陈述：isMultiplyPretransitive [IsPretransitive G α] {n : Nat} {a : α} : IsMultip
lyPretransitive G α n.succ ↔ IsMultiplyPretransitive (stabilizer G a) (SubMulAct
ion.ofStabilizer G a) n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubMulAction.ofStabilizer.snoc_last`：∀ {G : Type u_1} [inst : Group G] {
α : Type u_2} [inst_1 : MulAction G α] {a : α} {n : ℕ}   (x : Fin n ↪ ↥(SubMulAc
tion.ofStabilizer G a)), …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.smul_apply`：smul_apply [Group G] [MulAction G β] (g :
 G) (f : α ↪ β) (a : α) : (g • f) a = g • f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubMulAction.ofStabilizer.snoc_castSucc`：∀ {G : Type u_1} [inst : Group 
G] {α : Type u_2} [inst_1 : MulAction G α] {a : α} {n : ℕ}   (x : Fin n ↪ ↥(SubM
ulAction.ofStabilizer G a)) (…
· 使用引理 `SubMulAction.exists_smul_of_last_eq`：exists_smul_of_last_eq [IsPretransi
tive G α] {n : Nat} (a : α) (x : Fin n.succ ↪ α) : exists (g : G) (y : Fin n ↪ o
fStabilizer G a), g • x =…
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem isMultiplyPretransitive [IsPretransitive G α] {n : ℕ} {a : α} :
    IsMultiplyPretransitive G α n.succ ↔
      IsMultiplyPretransitive (stabilizer G a) (SubMulAction.ofStabilizer G a) n := by
  refine ⟨fun hn ↦ ⟨fun x y ↦ ?_⟩, fun hn ↦ ⟨fun x y ↦ ?_⟩⟩
  · obtain ⟨g, hgxy⟩ := exists_smul_eq G (ofStabilizer.snoc x) (ofStabilizer.snoc y)
    have hg : g ∈ stabilizer G a := by
      rw [DFunLike.ext_iff] at hgxy
      convert! hgxy (last n)
      simp [ofStabilizer.snoc_last]
    use ⟨g, hg⟩
    ext i
    simp only [smul_apply, SubMulAction.val_smul_of_tower, subgroup_smul_def]
    rw [← ofStabilizer.snoc_castSucc x, ← smul_apply, hgxy, ofStabilizer.snoc_castSucc]
  · -- gx • x = x1 :: a
    obtain ⟨gx, x1, hgx⟩ := exists_smul_of_last_eq G a x
    -- gy • y = y1 :: a
    obtain ⟨gy, y1, hgy⟩ := exists_smul_of_last_eq G a y
    -- g • x1 = y1,
    obtain ⟨g, hg⟩ := hn.exists_smul_eq x1 y1
    use gy⁻¹ * g * gx
    ext i
    simp only [mul_smul, smul_apply, inv_smul_eq_iff]
    simp only [← smul_apply _ _ i, hgy, hgx]
    simp only [smul_apply]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
    · simp [ofStabilizer.snoc_castSucc, ← hg, SetLike.val_smul, subgroup_smul_def]
    · simp only [ofStabilizer.snoc_last, ← hg]
      exact g.prop

end ofStabilizer

namespace ofFixingSubgroup

variable {G α : Type*} [Group G] [MulAction G α]

variable (G) in
/-- The `fixingSubgroup` of a finite subset of cardinal `d`
in an `n`-transitive action acts `n-d`-transitively on the complement. -/
@[to_additive /-- The `fixingSubgroup` of a finite subset of cardinal `d`
in an `n`-transitive additive action acts `n-d`-transitively on the complement. -/]
/-
**SubMulAction.ofFixingSubgroup.isMultiplyPretransitive** 是 Mathlib 中的一个定理，位于命名空
间 `SubMulAction.ofFixingSubgroup`。
形式化陈述：∀ (G : Type u_1) {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{m n : ℕ}   [Hn : MulAction.IsMultiplyPretransitive G α n] (s : Set α) [Finite ↑
s],   s.ncard + m = n → MulAction.IsMultiplyPretransitive (↥(fixingSubgroup G s)
) (↥(SubMulAction.ofFixingSubgroup G s)) m
参数：G : Type u_1；s : Set α；↥(fixingSubgroup G s)；↥(SubMulAction.ofFixingSubgroup 
G s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.card_eq`：card_eq [Finite α] [Finite β] : Nat.card α = Nat.card β 
↔ Nonempty (α ≃ β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubMulAction.ofFixingSubgroup.append_left`：∀ {M : Type u_1} {α : Type u_
2} [inst : Group M] [inst_1 : MulAction M α] {s : Set α} {n : ℕ} [inst_2 : Finit
e ↑s]   (x : Fin n ↪ ↥(SubMulAc…
· 使用定理 `Function.Embedding.smul_apply`：smul_apply [Group G] [MulAction G β] (g :
 G) (f : α ↪ β) (a : α) : (g • f) a = g • f a
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SubMulAction.instSMulMemClass`：∀ {R : Type u} {M : Type v} [inst : SMul 
R M], SMulMemClass (SubMulAction R M) R M
· 使用定理 `SetLike.val_smul`：∀ {S : Type u'} {R : Type u} {M : Type v} [inst : SMul
 R M] [inst_1 : SetLike S M] [hS : SMulMemClass S R M] (s : S)   (r : R) (x : ↥s
), ↑(r…
· 使用引理 `Subgroup.mk_smul`：mk_smul (g : G) (hg : g in S) (a : α) : (⟨g, hg⟩ : S) 
• a = g • a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem isMultiplyPretransitive {m n : ℕ} [Hn : IsMultiplyPretransitive G α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m = n) :
    IsMultiplyPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) m where
  exists_smul_eq x y := by
    have : IsMultiplyPretransitive G α (s.ncard + m) := by rw [hmn]; infer_instance
    have Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    set x' := ofFixingSubgroup.append x with hx
    set y' := ofFixingSubgroup.append y with hy
    obtain ⟨g, hg⟩ := exists_smul_eq G x' y'
    suffices g ∈ fixingSubgroup G s by
      use ⟨g, this⟩
      ext i
      rw [smul_apply, SetLike.val_smul, Subgroup.mk_smul]
      simp [← ofFixingSubgroup.append_right, ← smul_apply, ← hx, ← hy, hg]
    intro a
    set i := (Classical.choice Hs).symm a
    have ha : (Classical.choice Hs) i = a := by simp [i]
    rw [← ha]
    nth_rewrite 1 [← ofFixingSubgroup.append_left x i]
    rw [← ofFixingSubgroup.append_left y i, ← hy, ← hg, smul_apply, ← hx]

/-- The fixator of a finite subset of cardinal d in an n-transitive action
acts m transitively on the complement if d + m ≤ n. -/
@[to_additive /-- The fixator of a finite subset of cardinal d in an n-transitive additive action
acts m transitively on the complement if d + m ≤ n. -/]
/-
**SubMulAction.ofFixingSubgroup.isMultiplyPretransitive'** 是 Mathlib 中的一个定理，位于命名
空间 `SubMulAction.ofFixingSubgroup`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{m n : ℕ}   [MulAction.IsMultiplyPretransitive G α n] (s : Set α) [Finite ↑s],  
 s.ncard + m ≤ n →     ↑n ≤ ENat.card α →       MulAction.IsMultiplyPretransitiv
e (↥(fixingSubgroup G s)) (↥(SubMulAction.ofFixingSubgroup G s)) m
参数：s : Set α；↥(fixingSubgroup G s)；↥(SubMulAction.ofFixingSubgroup G s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.ofFixingSubgroup.isMultiplyPretransitive`：∀ (G : Type u_1) 
{α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] {m n : ℕ}   [Hn : MulAc
tion.IsMultiplyPretransitive G α n] (s : Se…
· 使用定理 `MulAction.isMultiplyPretransitive_of_le'`：isMultiplyPretransitive_of_le'
 {m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= ENat.card
 α) : IsMultiplyPretransitive …
-/
theorem isMultiplyPretransitive'
    {m n : ℕ} [IsMultiplyPretransitive G α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m ≤ n) (hn : (n : ENat) ≤ ENat.card α) :
    IsMultiplyPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s) m :=
  letI : IsMultiplyPretransitive G α (s.ncard + m) := isMultiplyPretransitive_of_le' hmn hn
  isMultiplyPretransitive G s rfl

end ofFixingSubgroup

end SubMulAction

namespace MulAction

section Index

open SubMulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

/-- For a multiply pretransitive action, computes the index
of the `fixingSubgroup` of a subset of adequate cardinality -/
/-
**MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_mul** 是 Mathlib 中的一个
定理，位于命名空间 `MulAction.IsMultiplyPretransitive`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
[Finite α] {k : ℕ},   MulAction.IsMultiplyPretransitive G α k →     ∀ {s : Set α
}, s.ncard = k → (fixingSubgroup G s).index * (Nat.card α - k).factorial = (Nat.
card α).factorial
参数：fixingSubgroup G s；Nat.card α - k；Nat.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.ncard_eq_zero`：∀ {α : Type u_1} {s : Set α}, autoParam s.Finite Set.
ncard_eq_zero._auto_1 → (s.ncard = 0 ↔ s = ∅)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `fixingSubgroup_empty`：fixingSubgroup_empty : fixingSubgroup M (∅ : Set α
) = ⊤
· 使用定理 `Subgroup.index_top`：index_top : (⊤ : Subgroup G).index = 1
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.is_one_pretransitive_iff`：is_one_pretransitive_iff : IsMultipl
yPretransitive G α 1 ↔ IsPretransitive G α
· 使用定理 `MulAction.isMultiplyPretransitive_of_le`：isMultiplyPretransitive_of_le {
m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= Nat.card α)
 [Finite α] : IsMultiplyPretr…
· 使用定理 `Nat.succ_le_succ_iff`：∀ {a b : ℕ}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Set.ncard_pos`：ncard_pos (hs : s.Finite
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `SubMulAction.fixingSubgroup_of_insert`：fixingSubgroup_of_insert (a : α) 
(s : Set (ofStabilizer M a)) : fixingSubgroup M (insert a ((fun x => x.val) '' s
)) = (fixingSubgroup (↥(sta…
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
For a multiply pretransitive action, computes the index
of the `fixingSubgroup` of a subset of adequate cardinality
-/
theorem IsMultiplyPretransitive.index_of_fixingSubgroup_mul
    [Finite α]
    {k : ℕ} (Hk : IsMultiplyPretransitive G α k)
    {s : Set α} (hs : s.ncard = k) :
    (fixingSubgroup G s).index * (Nat.card α - k).factorial =
      (Nat.card α).factorial := by
  induction k generalizing G α with
  | zero =>
    rw [Set.ncard_eq_zero] at hs
    simp [hs]
  | succ k hrec =>
    have hGX : IsPretransitive G α := by
      rw [← is_one_pretransitive_iff]
      apply isMultiplyPretransitive_of_le (n := k + 1)
      · rw [Nat.succ_le_succ_iff]; apply Nat.zero_le
      · rw [← hs, ← Set.ncard_univ]
        exact ncard_le_ncard s.subset_univ finite_univ
    have : s.Nonempty := by
      rw [← Set.ncard_pos, hs]
      exact succ_pos k
    obtain ⟨a, has⟩ := this
    let t : Set (SubMulAction.ofStabilizer G a) := Subtype.val ⁻¹' s
    have hat : Subtype.val '' t = s \ {a} := by
      rw [Set.image_preimage_eq_inter_range]
      simp only [Subtype.range_coe_subtype]
      rw [Set.sdiff_eq_compl_inter, Set.inter_comm]
      congr
    have hat' : s = insert a (Subtype.val '' t) := by
      rw [hat, Set.insert_sdiff_singleton, Set.insert_eq_of_mem has]
    have hfs := SubMulAction.fixingSubgroup_of_insert a t
    rw [← hat'] at hfs
    rw [hfs, Subgroup.index_map,
      MonoidHom.ker_eq_bot (stabilizer G a).subtype
        (by simp only [Subgroup.coe_subtype, Subtype.coe_injective])]
    simp only [sup_bot_eq, Subgroup.range_subtype]
    have htcard : t.ncard = k := by
      rw [← Nat.succ_inj, Nat.succ_eq_add_one, Nat.succ_eq_add_one, ← hs, hat', eq_comm]
      suffices ¬ a ∈ (Subtype.val '' t) by
        convert! Set.ncard_insert_of_notMem this ?_
        · rw [Set.ncard_image_of_injective _ Subtype.coe_injective]
        apply Set.toFinite
      intro h
      obtain ⟨⟨b, hb⟩, _, hb'⟩ := h
      apply hb
      simp only [← hb', Set.mem_singleton_iff]
    suffices (fixingSubgroup (stabilizer G a) t).index *
      (Nat.card α - 1 - k).factorial =
        (Nat.card α - 1).factorial by
      rw [add_comm k, Nat.mul_right_comm, ← Nat.sub_sub, this, mul_comm,
        index_stabilizer_of_transitive G a]
      exact Nat.mul_factorial_pred (card_ne_zero.mpr ⟨⟨a⟩, inferInstance⟩)
    convert! hrec (ofStabilizer.isMultiplyPretransitive.mp Hk) htcard
    all_goals { rw [nat_card_ofStabilizer_eq G a] }

/-- For a multiply pretransitive action,
computes the index of the `fixingSubgroup` of a subset
of adequate cardinality. -/
/-
**MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq** 是 Mathlib 中的一个定
理，位于命名空间 `MulAction.IsMultiplyPretransitive`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
[Finite α] (s : Set α),   MulAction.IsMultiplyPretransitive G α s.ncard →     (f
ixingSubgroup G s).index = (Nat.card α).choose s.ncard * s.ncard.factorial
参数：s : Set α；fixingSubgroup G s；Nat.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_of_mul_eq_mul_right`：∀ {n m k : ℕ}, 0 < m → n * m = k * m → n = k
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_mul`：∀ {G : Ty
pe u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] [Finite α] {k :
 ℕ},   MulAction.IsMultiplyPretransitive G α k →   …
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `Set.ncard_le_ncard`：ncard_le_ncard (hst : s subseteq t) (ht : t.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite

--- 原说明 ---
For a multiply pretransitive action,
computes the index of the `fixingSubgroup` of a subset
of adequate cardinality.
-/
theorem IsMultiplyPretransitive.index_of_fixingSubgroup_eq
    [Finite α] (s : Set α) (hMk : IsMultiplyPretransitive G α s.ncard) :
    (fixingSubgroup G s).index =
      Nat.choose (Nat.card α) s.ncard * s.ncard.factorial := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _)
  rw [hMk.index_of_fixingSubgroup_mul rfl, Nat.choose_mul_factorial_mul_factorial]
  rw [← ncard_univ]
  exact ncard_le_ncard (subset_univ s)

end Index

end MulAction

namespace Equiv.Perm

variable {α : Type*}

/-- For any two embeddings from a finite type into `β`, some permutation of `β` maps one to the
other. This is the action-form of `Equiv.Perm.exists_extending_pair`. -/
/-
**Equiv.Perm.exists_smul_eq_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {ι : Type u_2} [Finite ι] {β : Type u_3} (x y : ι ↪ β), ∃ σ, σ • x = y
参数：x y : ι ↪ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.exists_extending_pair`：∀ {α : Type u_1} {β : Type u_2} [Finit
e α] (f g : α → β),   Function.Injective f → Function.Injective g → ∃ σ, ∀ (a : 
α), σ (f a) = g a
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For any two embeddings from a finite type into `β`, some permutation of `β` maps
 one to the
other. This is the action-form of `Equiv.Perm.exists_extending_pair`.
-/
theorem exists_smul_eq_embedding {ι : Type*} [Finite ι] {β : Type*}
    (x y : ι ↪ β) : ∃ σ : Perm β, σ • x = y := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair x y x.injective y.injective
  exact ⟨σ, Function.Embedding.ext fun i => by simp [Function.Embedding.smul_apply, hσ]⟩

variable (α) in
/-- The permutation group `Equiv.Perm α` acts `n`-pretransitively on `α` for all `n`. -/
/-
**Equiv.Perm.isMultiplyPretransitive** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ (α : Type u_1) (n : ℕ), MulAction.IsMultiplyPretransitive (Equiv.Perm α)
 α n
参数：α : Type u_1；n : ℕ；Equiv.Perm α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.isMultiplyPretransitive_iff`：isMultiplyPretransitive_iff {n : 
Nat} : IsMultiplyPretransitive G α n ↔ forall x y : Fin n ↪ α, exists g : G, g •
 x = y
· 使用定理 `Equiv.Perm.exists_smul_eq_embedding`：∀ {ι : Type u_2} [Finite ι] {β : Ty
pe u_3} (x y : ι ↪ β), ∃ σ, σ • x = y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The permutation group `Equiv.Perm α` acts `n`-pretransitively on `α` for all `n`
.
-/
theorem isMultiplyPretransitive (n : ℕ) :
    IsMultiplyPretransitive (Perm α) α n := by
  rw [isMultiplyPretransitive_iff]
  exact exists_smul_eq_embedding

/-- The action of the permutation group of `α` on `α` is preprimitive -/
/-
**Equiv.Perm.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the permutation group of `α` on `α` is preprimitive
-/
instance : IsPreprimitive (Perm α) α :=
  isPreprimitive_of_is_two_pretransitive (isMultiplyPretransitive _ _)

-- This is optimal, `AlternatingGroup α` is `Nat.card α - 2`-pretransitive.
/-- A subgroup of `Perm α` is `⊤` if(f) it is `(Nat.card α - 1)`-pretransitive. -/
/-
**Equiv.Perm.eq_top_of_isMultiplyPretransitive** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm`。
形式化陈述：∀ {α : Type u_1} [Finite α] {G : Subgroup (Equiv.Perm α)},   MulAction.IsM
ultiplyPretransitive (↥G) α (Nat.card α - 1) → G = ⊤
参数：Equiv.Perm α；↥G；Nat.card α - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Embedding.ext_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f g : α ↪ β
}, f = g ↔ ∀ (x : α), f x = g x
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p

--- 原说明 ---
A subgroup of `Perm α` is `⊤` if(f) it is `(Nat.card α - 1)`-pretransitive.
-/
theorem eq_top_of_isMultiplyPretransitive [Finite α] {G : Subgroup (Equiv.Perm α)}
    (hmt : IsMultiplyPretransitive G α (Nat.card α - 1)) : G = ⊤ := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card] at hmt
  let j : Fin (Fintype.card α - 1) ↪ Fin (Fintype.card α) :=
    (Fin.castLEEmb ((Fintype.card α).sub_le 1))
  rw [eq_top_iff]
  intro k _
  let x : Fin (Fintype.card α) ↪ α := (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  let x' := j.trans x
  obtain ⟨g, hg'⟩ := exists_smul_eq G x' (k • x')
  suffices k = g by rw [this]; exact SetLike.coe_mem g
  have hx (x : Fin (Fintype.card α) ↪ α) : Function.Surjective x.toFun := by
    apply Function.Bijective.surjective
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨EmbeddingLike.injective x, Fintype.card_fin (Fintype.card α)⟩
  have hgk' (i : Fin (Fintype.card α)) (hi : i.val < Fintype.card α - 1) :
      (g • x) i = (k • x) i :=
    Function.Embedding.ext_iff.mp hg' ⟨i.val, hi⟩
  have hgk (i : Fin (Fintype.card α)) : (g • x) i = (k • x) i := by
    rcases lt_or_eq_of_le (le_sub_one_of_lt i.prop) with hi | hi
    · exact hgk' i hi
    · obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i)
      rcases lt_or_eq_of_le (le_sub_one_of_lt j.prop) with hj | hj
      · suffices i = j by
          rw [← this, ← hi] at hj
          exact (lt_irrefl _ hj).elim
        apply EmbeddingLike.injective (g • x)
        rw [hgk' j hj, hxj]
      · rw [← hxj]
        apply congr_arg
        rw [Fin.ext_iff, hi, hj]
  ext a
  obtain ⟨i, rfl⟩ := (hx x) a
  specialize hgk i
  simp only [Function.Embedding.smul_apply, Equiv.Perm.smul_def] at hgk
  simp [← hgk, Subgroup.smul_def, Perm.smul_def]

end Equiv.Perm

namespace alternatingGroup

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- The `alternatingGroup` on `α` is `(Nat.card α - 2)`-pretransitive. -/
/-
**alternatingGroup.isMultiplyPretransitive** 是 Mathlib 中的一个定理，位于命名空间 `alternatin
gGroup`。
形式化陈述：∀ (α : Type u_1) [inst : Fintype α] [inst_1 : DecidableEq α],   MulAction.
IsMultiplyPretransitive (↥(alternatingGroup α)) α (Nat.card α - 2)
参数：α : Type u_1；↥(alternatingGroup α)；Nat.card α - 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MulAction.is_zero_pretransitive`：is_zero_pretransitive {n : Type*} [IsEm
pty n] : IsPretransitive G (n ↪ α)
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Equiv.Perm.isMultiplyPretransitive`：∀ (α : Type u_1) (n : ℕ), MulAction.
IsMultiplyPretransitive (Equiv.Perm α) α n
· 使用定理 `MulAction.isMultiplyPretransitive_of_le`：isMultiplyPretransitive_of_le {
m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= Nat.card α)
 [Finite α] : IsMultiplyPretr…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `tsub_tsub_cancel_of_le`：tsub_tsub_cancel_of_le (h : a <= b) : b - (b - a
) = a
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_two`：card_eq_two : #s = 2 ↔ exists x y, x != y ∧ s = {x, 
y}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The `alternatingGroup` on `α` is `(Nat.card α - 2)`-pretransitive.
-/
theorem isMultiplyPretransitive :
    IsMultiplyPretransitive (alternatingGroup α) α (Nat.card α - 2) := by
  rcases lt_or_ge (Nat.card α) 2 with h2 | h2
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h2)]
    apply is_zero_pretransitive
  have h2le : Nat.card α - 2 ≤ Nat.card α := sub_le (Nat.card α) 2
  have := Equiv.Perm.isMultiplyPretransitive α (Nat.card α)
  have : IsMultiplyPretransitive (Equiv.Perm α) α (Nat.card α - 2) :=
    MulAction.isMultiplyPretransitive_of_le h2le le_rfl
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_eq (Equiv.Perm α) x y
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
  · exact ⟨⟨g, h⟩, hg⟩
  · have : (Finset.univ.image x)ᶜ.card = 2 := by
      rw [Finset.card_compl, Finset.univ.card_image_of_injective (by exact x.2), Finset.card_univ,
        ← Nat.card_eq_fintype_card, Fintype.card_fin, tsub_tsub_cancel_of_le h2]
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp this
    refine ⟨⟨g * Equiv.swap a b, by simp [h, hab]⟩, ?_⟩
    ext i
    have h : x i ∈ Finset.univ.image x := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [← Finset.notMem_compl, hs, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    simp [Equiv.swap_apply_of_ne_of_ne h.1 h.2, ← hg]

/-- A subgroup of `Equiv.Perm α` which is (card α - 2)-pretransitive
contains `alternatingGroup α`. -/
/-
**alternatingGroup._root_.IsMultiplyPretransitive.alternatingGroup_le** 是 Mathli
b 中的一个定理，位于命名空间 `alternatingGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of `Equiv.Perm α` which is (card α - 2)-pretransitive
contains `alternatingGroup α`.
-/
theorem _root_.IsMultiplyPretransitive.alternatingGroup_le
    (G : Subgroup (Equiv.Perm α))
    (hmt : IsMultiplyPretransitive G α (Nat.card α - 2)) :
    alternatingGroup α ≤ G := by
  rcases Nat.lt_or_ge (Nat.card α) 2 with hα1 | hα
  · -- Nat.card α  < 2
    rw [eq_bot_of_card_le_two hα1.le]
    exact bot_le
  -- 2 ≤ Nat.card α
  apply Equiv.Perm.alternatingGroup_le_of_index_le_two
  -- one picks up a set of cardinality (card α - 2)
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq (s := (Set.univ : Set α)) (n := Nat.card α - 2)
      (by rw [Set.ncard_univ]; exact sub_le (Nat.card α) 2)
  rw [← hs] at hmt
  -- The index of (fixingSubgroup G s) is (card α)!/2
  have := hmt.index_of_fixingSubgroup_mul rfl
  rw [hs, Nat.sub_sub_self hα, factorial_two] at this
  -- conclude
  rw [← mul_le_mul_iff_of_pos_left (a := Nat.card G) card_pos,
    Subgroup.card_mul_index, ← (fixingSubgroup G s).index_mul_card,
    mul_assoc, mul_comm _ 2, ← mul_assoc]
  rw [this, Nat.card_perm]
  refine Nat.le_mul_of_pos_right (Nat.card α)! card_pos

/-- The alternating group on 3 letters or more acts transitively. -/
/-
**alternatingGroup.isPretransitive_of_three_le_card** 是 Mathlib 中的一个定理，位于命名空间 `a
lternatingGroup`。
形式化陈述：∀ (α : Type u_1) [inst : Fintype α] [inst_1 : DecidableEq α],   3 ≤ Nat.ca
rd α → MulAction.IsPretransitive (↥(alternatingGroup α)) α
参数：α : Type u_1；↥(alternatingGroup α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.is_one_pretransitive_iff`：is_one_pretransitive_iff : IsMultipl
yPretransitive G α 1 ↔ IsPretransitive G α
· 使用定理 `alternatingGroup.isMultiplyPretransitive`：∀ (α : Type u_1) [inst : Finty
pe α] [inst_1 : DecidableEq α],   MulAction.IsMultiplyPretransitive (↥(alternati
ngGroup α)) α (Nat.card α - 2)
· 使用定理 `MulAction.isMultiplyPretransitive_of_le`：isMultiplyPretransitive_of_le {
m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= Nat.card α)
 [Finite α] : IsMultiplyPretr…
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The alternating group on 3 letters or more acts transitively.
-/
theorem isPretransitive_of_three_le_card (h : 3 ≤ Nat.card α) :
    IsPretransitive (alternatingGroup α) α := by
  rw [← is_one_pretransitive_iff]
  let := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rwa [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_trans (by norm_num) h)]

/-- The action of the alternating group has trivial blocks.

This holds for any `α`, even when `Nat.card α ≤ 2` and the action
is not preprimitive, because it is not pretransitive. -/
/-
**alternatingGroup.isTrivialBlock_of_isBlock** 是 Mathlib 中的一个定理，位于命名空间 `alternat
ingGroup`。
形式化陈述：∀ (α : Type u_1) [inst : Fintype α] [inst_1 : DecidableEq α] {B : Set α}, 
  MulAction.IsBlock (↥(alternatingGroup α)) B → MulAction.IsTrivialBlock B
参数：α : Type u_1；↥(alternatingGroup α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `MulAction.isTrivialBlock_of_card_le_two`：isTrivialBlock_of_card_le_two [
Finite X] (hX : Nat.card X <= 2) (B : Set X) : IsTrivialBlock B
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `alternatingGroup.isPretransitive_of_three_le_card`：∀ (α : Type u_1) [ins
t : Fintype α] [inst_1 : DecidableEq α],   3 ≤ Nat.card α → MulAction.IsPretrans
itive (↥(alternatingGroup α)) α
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MulAction.IsPreprimitive.of_prime_card`：of_prime_card [hGX : IsPretransi
tive G X] (hp : Nat.Prime (Nat.card X)) : IsPreprimitive G X
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.IsPreprimitive.isTrivialBlock_of_isBlock`：∀ {G : Type u_1} {X 
: Type u_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X] {B : Set X},
   MulAction.IsBlock G B → MulAction.IsT…
· 使用定理 `MulAction.isPreprimitive_of_is_two_pretransitive`：isPreprimitive_of_is_t
wo_pretransitive (h2 : IsMultiplyPretransitive G α 2) : IsPreprimitive G α
· 使用定理 `alternatingGroup.isMultiplyPretransitive`：∀ (α : Type u_1) [inst : Finty
pe α] [inst_1 : DecidableEq α],   MulAction.IsMultiplyPretransitive (↥(alternati
ngGroup α)) α (Nat.card α - 2)
· 使用定理 `MulAction.isMultiplyPretransitive_of_le`：isMultiplyPretransitive_of_le {
m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= Nat.card α)
 [Finite α] : IsMultiplyPretr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n

--- 原说明 ---
The action of the alternating group has trivial blocks.

This holds for any `α`, even when `Nat.card α ≤ 2` and the action
is not preprimitive, because it is not pretransitive.
-/
theorem isTrivialBlock_of_isBlock {B : Set α} (hB : IsBlock (alternatingGroup α) B) :
    IsTrivialBlock B := by
  rcases le_or_gt (Nat.card α) 2 with h2 | h2
  · exact isTrivialBlock_of_card_le_two h2 B
  rcases le_or_gt (Nat.card α) 3 with h3 | h4
  · replace h3 : Nat.card α = 3 := le_antisymm h3 h2
    have : IsPretransitive (alternatingGroup α) α := isPretransitive_of_three_le_card α h3.ge
    have : IsPreprimitive (alternatingGroup α) α := IsPreprimitive.of_prime_card (h3 ▸ prime_three)
    exact this.isTrivialBlock_of_isBlock hB
  -- IsTrivialBlock hB, for 4 ≤ Nat.card α
  suffices IsPreprimitive (alternatingGroup α) α by
    apply IsPreprimitive.isTrivialBlock_of_isBlock hB
  apply isPreprimitive_of_is_two_pretransitive
  let := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rwa [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_of_lt h2)]

/-- The alternating group on 3 letters or more acts primitively -/
/-
**alternatingGroup.isPreprimitive_of_three_le_card** 是 Mathlib 中的一个定理，位于命名空间 `al
ternatingGroup`。
形式化陈述：∀ (α : Type u_1) [inst : Fintype α] [inst_1 : DecidableEq α],   3 ≤ Nat.ca
rd α → MulAction.IsPreprimitive (↥(alternatingGroup α)) α
参数：α : Type u_1；↥(alternatingGroup α)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `alternatingGroup.isPretransitive_of_three_le_card`：∀ (α : Type u_1) [ins
t : Fintype α] [inst_1 : DecidableEq α],   3 ≤ Nat.card α → MulAction.IsPretrans
itive (↥(alternatingGroup α)) α
· 使用定理 `alternatingGroup.isTrivialBlock_of_isBlock`：∀ (α : Type u_1) [inst : Fin
type α] [inst_1 : DecidableEq α] {B : Set α},   MulAction.IsBlock (↥(alternating
Group α)) B → MulAction.IsTrivia…

--- 原说明 ---
The alternating group on 3 letters or more acts primitively
-/
theorem isPreprimitive_of_three_le_card (h : 3 ≤ Nat.card α) :
    IsPreprimitive (alternatingGroup α) α :=
  letI := isPretransitive_of_three_le_card α h
  { isTrivialBlock_of_isBlock := isTrivialBlock_of_isBlock α }

end alternatingGroup

