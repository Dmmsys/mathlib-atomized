/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, David Loeffler
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Vertical line test for group homs

This file proves the vertical line test for monoid homomorphisms/isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`.

Furthermore, if `f` is also surjective on the second factor and its image intersects every
"horizontal line" `{(h, i) | h : H}` at most once, then `f'` is actually an isomorphism
`f' : H ≃ I`.

We also prove specialised versions when `f` is the inclusion of a subgroup of the direct product.
(The version for general homomorphisms can easily be reduced to this special case, but the
homomorphism version is more flexible in applications.)
-/

@[expose] public section

open Function Set

variable {G H I : Type*}

section Monoid
variable [Monoid G] [Monoid H] [Monoid I]

namespace MonoidHom

/-- The graph of a monoid homomorphism as a submonoid.

See also `MonoidHom.graph` for the graph as a subgroup. -/
@[to_additive
/-- The graph of a monoid homomorphism as a submonoid.

See also `AddMonoidHom.graph` for the graph as a subgroup. -/]
/-
**MonoidHom.mgraph** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：mgraph (f : G ->* H) : Submonoid (G × H) where carrier
参数：f : G ->* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mgraph (f : G →* H) : Submonoid (G × H) where
  carrier := {x | f x.1 = x.2}
  one_mem' := map_one f
  mul_mem' {x y} := by simp +contextual

-- TODO: Can `to_additive` be smarter about `simps`?
attribute [simps! coe] mgraph
attribute [simps! coe] AddMonoidHom.mgraph
attribute [to_additive existing] coe_mgraph

@[to_additive (attr := simp)]
/-
**MonoidHom.mem_mgraph** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mem_mgraph {f : G ->* H} {x : G × H} : x in f.mgraph ↔ f x.1 = x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_mgraph {f : G →* H} {x : G × H} : x ∈ f.mgraph ↔ f x.1 = x.2 := .rfl

@[to_additive mgraph_eq_mrange_prod]
/-
**MonoidHom.mgraph_eq_mrange_prod** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mgraph_eq_mrange_prod (f : G ->* H) : f.mgraph = mrange ((id _).prod f)
参数：f : G ->* H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mgraph_eq_mrange_prod (f : G →* H) : f.mgraph = mrange ((id _).prod f) := by aesop

/-- **Vertical line test** for monoid homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`. -/
@[to_additive /-- **Vertical line test** for monoid homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some monoid homomorphism `f' : H → I`. -/]
/-
**MonoidHom.exists_mrange_eq_mgraph** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：exists_mrange_eq_mgraph {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f)
) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f g₁).2 = (f g₂).2) : exists f' : 
H ->* I, mrange f = f'.mgraph
参数：hf₁ : Surjective (Prod.fst ∘ f)；hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f 
g₁).2 = (f g₂).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.exists_range_eq_graphOn_univ`：exists_range_eq_graphOn_univ {f : α ->
 β × γ} (hf₁ : Surjective (Prod.fst ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).
1 -> (f g₁).2 = (f g₂)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma exists_mrange_eq_mgraph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →* I, mrange f = f'.mgraph := by
  obtain ⟨f', hf'⟩ := exists_range_eq_graphOn_univ hf₁ hf
  simp only [Set.ext_iff, Set.mem_range, mem_graphOn, mem_univ, true_and, Prod.forall] at hf'
  use
  { toFun := f'
    map_one' := (hf' _ _).1 ⟨1, map_one _⟩
    map_mul' := by
      simp_rw [hf₁.forall]
      rintro g₁ g₂
      exact (hf' _ _).1 ⟨g₁ * g₂, by simp [Prod.ext_iff, (hf' (f _).1 _).1 ⟨_, rfl⟩]⟩ }
  simpa [SetLike.ext_iff] using hf'

/-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some monoid
isomorphism `f' : H ≃ I`. -/
@[to_additive /-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of monoids. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some
monoid isomorphism `f' : H ≃ I`. -/]
/-
**MonoidHom.exists_mulEquiv_mrange_eq_mgraph** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHo
m`。
形式化陈述：exists_mulEquiv_mrange_eq_mgraph {f : G ->* H × I} (hf₁ : Surjective (Prod
.fst ∘ f)) (hf₂ : Surjective (Prod.snd ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g
₂).1 ↔ (f g₁).2 = (f g₂).2) : exists e : H ≃* I, mrange f = e.toMonoidHom.mgraph
参数：hf₁ : Surjective (Prod.fst ∘ f)；hf₂ : Surjective (Prod.snd ∘ f)；hf : forall g
₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.exists_mrange_eq_mgraph`：exists_mrange_eq_mgraph {f : G ->* H 
× I} (hf₁ : Surjective (Prod.fst ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -
> (f g₁).2 = (f g₂).2) …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
-/
lemma exists_mulEquiv_mrange_eq_mgraph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃* I, mrange f = e.toMonoidHom.mgraph := by
  obtain ⟨e₁, he₁⟩ := f.exists_mrange_eq_mgraph hf₁ fun _ _ ↦ (hf _ _).1
  obtain ⟨e₂, he₂⟩ := (MulEquiv.prodComm.toMonoidHom.comp f).exists_mrange_eq_mgraph (by simpa) <|
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [SetLike.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_eq_iff_eq_swap])
  exact ⟨
  { toFun := e₁
    map_mul' := e₁.map_mul'
    invFun := e₂
    left_inv := fun h ↦ by rw [← he₁₂]
    right_inv := fun i ↦ by rw [he₁₂] }, he₁⟩

end MonoidHom

/-- **Vertical line test** for monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` maps bijectively to the
first factor. Then `G` is the graph of some monoid homomorphism `f : H → I`. -/
@[to_additive /-- **Vertical line test** for additive monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` surjects onto the first
factor and `G` intersects every "vertical line" `{(h, i) | i : I}` at most once. Then `G` is the
graph of some monoid homomorphism `f : H → I`. -/]
/-
**Submonoid.exists_eq_mgraph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.exists_eq_mgraph {G : Submonoid (H × I)} (hG₁ : Bijective (Prod.
fst ∘ G.subtype)) : exists f : H ->* I, G = f.mgraph
参数：H × I；hG₁ : Bijective (Prod.fst ∘ G.subtype)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submonoid.mrange_subtype`：mrange_subtype (s : Submonoid M) : mrange s.su
btype = s
· 使用引理 `MonoidHom.exists_mrange_eq_mgraph`：exists_mrange_eq_mgraph {f : G ->* H 
× I} (hf₁ : Surjective (Prod.fst ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -
> (f g₁).2 = (f g₂).2) …
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
lemma Submonoid.exists_eq_mgraph {G : Submonoid (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →* I, G = f.mgraph := by
  simpa using MonoidHom.exists_mrange_eq_mgraph hG₁.surjective
    fun a b h ↦ congr_arg (Prod.snd ∘ G.subtype) (hG₁.injective h)

/-- **Goursat's lemma** for monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that the natural maps from `G` to
both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃* I`. -/
@[to_additive /-- **Goursat's lemma** for additive monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of additive monoids. Assume that the natural maps from
`G` to both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃+ I`. -/]
/-
**Submonoid.exists_mulEquiv_eq_mgraph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.exists_mulEquiv_eq_mgraph {G : Submonoid (H × I)} (hG₁ : Bijecti
ve (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) : exists e :
 H ≃* I, G = e.toMonoidHom.mgraph
参数：H × I；hG₁ : Bijective (Prod.fst ∘ G.subtype)；hG₂ : Bijective (Prod.snd ∘ G.su
btype)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submonoid.mrange_subtype`：mrange_subtype (s : Submonoid M) : mrange s.su
btype = s
· 使用引理 `MonoidHom.exists_mulEquiv_mrange_eq_mgraph`：exists_mulEquiv_mrange_eq_mg
raph {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f)) (hf₂ : Surjective (Prod
.snd ∘ f)) (hf : forall g₁ g₂, (…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
lemma Submonoid.exists_mulEquiv_eq_mgraph {G : Submonoid (H × I)}
    (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃* I, G = e.toMonoidHom.mgraph := by
  simpa using MonoidHom.exists_mulEquiv_mrange_eq_mgraph hG₁.surjective hG₂.surjective
    fun _ _ ↦ hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

end Monoid

section Group
variable [Group G] [Group H] [Group I]

namespace MonoidHom

/-- The graph of a group homomorphism as a subgroup.

See also `MonoidHom.mgraph` for the graph as a submonoid. -/
@[to_additive
/-- The graph of a group homomorphism as a subgroup.

See also `AddMonoidHom.mgraph` for the graph as a submonoid. -/]
/-
**MonoidHom.graph** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：graph (f : G ->* H) : Subgroup (G × H) where toSubmonoid
参数：f : G ->* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def graph (f : G →* H) : Subgroup (G × H) where
  toSubmonoid := f.mgraph
  inv_mem' {x} := by simp +contextual

-- TODO: Can `to_additive` be smarter about `simps`?
attribute [simps! coe toSubmonoid] graph
attribute [simps! coe toAddSubmonoid] AddMonoidHom.graph
attribute [to_additive existing] coe_graph graph_toSubmonoid

@[to_additive]
/-
**MonoidHom.mem_graph** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mem_graph {f : G ->* H} {x : G × H} : x in f.graph ↔ f x.1 = x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_graph {f : G →* H} {x : G × H} : x ∈ f.graph ↔ f x.1 = x.2 := .rfl

@[to_additive graph_eq_range_prod]
/-
**MonoidHom.graph_eq_range_prod** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：graph_eq_range_prod (f : G ->* H) : f.graph = range ((id _).prod f)
参数：f : G ->* H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma graph_eq_range_prod (f : G →* H) : f.graph = range ((id _).prod f) := by aesop

/-- **Vertical line test** for group homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some group homomorphism `f' : H → I`. -/
@[to_additive /-- **Vertical line test** for group homomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on the
first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at most
once. Then the image of `f` is the graph of some group homomorphism `f' : H → I`. -/]
/-
**MonoidHom.exists_range_eq_graph** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：exists_range_eq_graph {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f)) 
(hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f g₁).2 = (f g₂).2) : exists f' : H 
->* I, range f = f'.graph
参数：hf₁ : Surjective (Prod.fst ∘ f)；hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f 
g₁).2 = (f g₂).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MonoidHom.exists_mrange_eq_mgraph`：exists_mrange_eq_mgraph {f : G ->* H 
× I} (hf₁ : Surjective (Prod.fst ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -
> (f g₁).2 = (f g₂).2) …
-/
lemma exists_range_eq_graph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →* I, range f = f'.graph := by
  simpa [SetLike.ext_iff] using! exists_mrange_eq_mgraph hf₁ hf

/-- **Line test** for group isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some group
isomorphism `f' : H ≃ I`. -/
@[to_additive /-- **Line test** for monoid isomorphisms.

Let `f : G → H × I` be a homomorphism to a product of groups. Assume that `f` is surjective on both
factors and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` and every
"horizontal line" `{(h, i) | h : H}` at most once. Then the image of `f` is the graph of some
group isomorphism `f' : H ≃ I`. -/]
/-
**MonoidHom.exists_mulEquiv_range_eq_graph** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`
。
形式化陈述：exists_mulEquiv_range_eq_graph {f : G ->* H × I} (hf₁ : Surjective (Prod.f
st ∘ f)) (hf₂ : Surjective (Prod.snd ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂)
.1 ↔ (f g₁).2 = (f g₂).2) : exists e : H ≃* I, range f = e.toMonoidHom.graph
参数：hf₁ : Surjective (Prod.fst ∘ f)；hf₂ : Surjective (Prod.snd ∘ f)；hf : forall g
₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MonoidHom.exists_mulEquiv_mrange_eq_mgraph`：exists_mulEquiv_mrange_eq_mg
raph {f : G ->* H × I} (hf₁ : Surjective (Prod.fst ∘ f)) (hf₂ : Surjective (Prod
.snd ∘ f)) (hf : forall g₁ g₂, (…
-/
lemma exists_mulEquiv_range_eq_graph {f : G →* H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃* I, range f = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using! exists_mulEquiv_mrange_eq_mgraph hf₁ hf₂ hf

end MonoidHom

/-- **Vertical line test** for group homomorphisms.

Let `G ≤ H × I` be a subgroup of a product of monoids. Assume that `G` maps bijectively to the
first factor. Then `G` is the graph of some monoid homomorphism `f : H → I`. -/
@[to_additive /-- **Vertical line test** for additive monoid homomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that `G` surjects onto the first
factor and `G` intersects every "vertical line" `{(h, i) | i : I}` at most once. Then `G` is the
graph of some monoid homomorphism `f : H → I`. -/]
/-
**Subgroup.exists_eq_graph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.exists_eq_graph {G : Subgroup (H × I)} (hG₁ : Bijective (Prod.fst
 ∘ G.subtype)) : exists f : H ->* I, G = f.graph
参数：H × I；hG₁ : Bijective (Prod.fst ∘ G.subtype)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Submonoid.exists_eq_mgraph`：Submonoid.exists_eq_mgraph {G : Submonoid (H
 × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype)) : exists f : H ->* I, G = f.mgra
ph
-/
lemma Subgroup.exists_eq_graph {G : Subgroup (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →* I, G = f.graph := by
  simpa [SetLike.ext_iff] using! Submonoid.exists_eq_mgraph hG₁

/-- **Goursat's lemma** for monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of monoids. Assume that the natural maps from `G` to
both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃* I`. -/
@[to_additive /-- **Goursat's lemma** for additive monoid isomorphisms.

Let `G ≤ H × I` be a submonoid of a product of additive monoids. Assume that the natural maps from
`G` to both factors are bijective. Then `G` is the graph of some isomorphism `f : H ≃+ I`. -/]
/-
**Subgroup.exists_mulEquiv_eq_graph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.exists_mulEquiv_eq_graph {G : Subgroup (H × I)} (hG₁ : Bijective 
(Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) : exists e : H 
≃* I, G = e.toMonoidHom.graph
参数：H × I；hG₁ : Bijective (Prod.fst ∘ G.subtype)；hG₂ : Bijective (Prod.snd ∘ G.su
btype)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Submonoid.exists_mulEquiv_eq_mgraph`：Submonoid.exists_mulEquiv_eq_mgraph
 {G : Submonoid (H × I)} (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijecti
ve (Prod.snd ∘ G.subtype)…
-/
lemma Subgroup.exists_mulEquiv_eq_graph {G : Subgroup (H × I)}
    (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃* I, G = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using! Submonoid.exists_mulEquiv_eq_mgraph hG₁ hG₂

end Group

