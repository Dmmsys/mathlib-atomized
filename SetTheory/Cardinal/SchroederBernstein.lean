/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.Zorn

/-!
# Schröder-Bernstein theorem, well-ordering of cardinals

This file proves the Schröder-Bernstein theorem (see `schroeder_bernstein`), the well-ordering of
cardinals (see `min_injective`) and the totality of their order (see `total`).

## Notes

Cardinals are naturally ordered by `α ≤ β ↔ ∃ f : a → β, Injective f`:
* `schroeder_bernstein` states that, given injections `α → β` and `β → α`, one can get a
  bijection `α → β`. This corresponds to the antisymmetry of the order.
* The order is also well-founded: any nonempty set of cardinals has a minimal element.
  `min_injective` states that by saying that there exists an element of the set that injects into
  all others.

Cardinals are defined and further developed in the folder `SetTheory.Cardinal`.
-/

public section


open Set Function

universe u v

namespace Function

namespace Embedding

section antisymm

variable {α : Type u} {β : Type v}

/-- **The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α` that satisfy a pointwise property `R`, we can get a bijection
`α → β` that satisfies that same pointwise property. -/
/-
**Function.Embedding.schroeder_bernstein_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion.Embedding`。
形式化陈述：schroeder_bernstein_of_rel {f : α -> β} {g : β -> α} (hf : Function.Inject
ive f) (hg : Function.Injective g) (R : α -> β -> Prop) (hp₁ : forall a : α, R a
 (f a)) (hp₂ : forall b : β, R (g b) b) : exists h : α -> β, Bijective h ∧ foral
l a : α, R a (h a)
参数：hf : Function.Injective f；hg : Function.Injective g；R : α -> β -> Prop；hp₁ : 
forall a : α, R a (f a)；hp₂ : forall b : β, R (g b) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `OrderHom.map_lfp`：map_lfp : f f.lfp = f.lfp
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.LeftInverse.image_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β} {g : β → α}, Function.LeftInverse g f → ∀ (s : Set α), g '' f '' s = s
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Set.range_piecewise`：range_piecewise (f g : α -> β) : range (s.piecewise
 f g) = f '' s union g '' sᶜ
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injective_piecewise_iff`：injective_piecewise_iff {f g : α -> β} : In
jective (s.piecewise f g) ↔ InjOn f s ∧ InjOn g sᶜ ∧ forall x in s, forall y ∉ s
, f x != g y
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Set.piecewise.eq_1`：∀ {α : Type u} {β : α → Sort v} (s : Set α) (f g : (
i : α) → β i) [inst : (j : α) → Decidable (j ∈ s)] (i : α),   s.piecewise f g i 
= if i ∈…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
**The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α` that satisfy a pointwise property `R`, we c
an get a bijection
`α → β` that satisfies that same pointwise property.
-/
theorem schroeder_bernstein_of_rel {f : α → β} {g : β → α} (hf : Function.Injective f)
    (hg : Function.Injective g) (R : α → β → Prop) (hp₁ : ∀ a : α, R a (f a))
    (hp₂ : ∀ b : β, R (g b) b) :
    ∃ h : α → β, Bijective h ∧ ∀ a : α, R a (h a) := by
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty α := Function.isEmpty f
    exact ⟨_, ((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).bijective, by simp⟩
  set F : Set α →o Set α :=
    { toFun := fun s => (g '' (f '' s)ᶜ)ᶜ
      monotone' := fun s t hst => by dsimp at hst ⊢; gcongr }
  set s : Set α := F.lfp
  have hs : (g '' (f '' s)ᶜ)ᶜ = s := F.map_lfp
  have hns : g '' (f '' s)ᶜ = sᶜ := compl_injective (by simp [hs])
  set g' := invFun g
  have g'g : LeftInverse g' g := leftInverse_invFun hg
  have hg'ns : g' '' sᶜ = (f '' s)ᶜ := by rw [← hns, g'g.image_image]
  set h : α → β := s.piecewise f g'
  have : Surjective h := by rw [← range_eq_univ, range_piecewise, hg'ns, union_compl_self]
  have : Injective h := by
    refine (injective_piecewise_iff _).2 ⟨hf.injOn, ?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨x', _, rfl⟩ : x ∈ g '' (f '' s)ᶜ := by rwa [hns]
      obtain ⟨y', _, rfl⟩ : y ∈ g '' (f '' s)ᶜ := by rwa [hns]
      rw [g'g _, g'g _] at hxy
      rw [hxy]
    · intro x hx y hy hxy
      obtain ⟨y', hy', rfl⟩ : y ∈ g '' (f '' s)ᶜ := by rwa [hns]
      rw [g'g _] at hxy
      exact hy' ⟨x, hx, hxy⟩
  refine ⟨h, ⟨‹Injective h›, ‹Surjective h›⟩, fun a ↦ ?_⟩
  simp only [h, Set.piecewise, g']
  split
  · exact hp₁ a
  · have : g (invFun g a) = a := by
      have : a ∈ g '' (f '' s)ᶜ := by grind
      obtain ⟨x, _, hx⟩ := mem_image _ _ _ |>.mp this
      exact Function.invFun_eq ⟨x, hx⟩
    grind

/-- **The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α`, we can get a bijection `α → β`. -/
/-
**Function.Embedding.schroeder_bernstein** 是 Mathlib 中的一个定理，位于命名空间 `Function.Emb
edding`。
形式化陈述：schroeder_bernstein {f : α -> β} {g : β -> α} (hf : Function.Injective f) 
(hg : Function.Injective g) : exists h : α -> β, Bijective h
参数：hf : Function.Injective f；hg : Function.Injective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.schroeder_bernstein_of_rel`：schroeder_bernstein_of_re
l {f : α -> β} {g : β -> α} (hf : Function.Injective f) (hg : Function.Injective
 g) (R : α -> β -> Prop) (hp₁ : for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
**The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α`, we can get a bijection `α → β`.
-/
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Function.Injective f)
    (hg : Function.Injective g) : ∃ h : α → β, Bijective h := by
  obtain ⟨f, hf, _⟩ := schroeder_bernstein_of_rel hf hg (fun x y ↦ True) (by simp) (by simp)
  exact ⟨f, hf⟩

/-- **The Schröder-Bernstein Theorem**: Given embeddings `α ↪ β` and `β ↪ α`, there exists an
equivalence `α ≃ β`. -/
/-
**Function.Embedding.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：antisymm : (α ↪ β) -> (β ↪ α) -> Nonempty (α ≃ β) | ⟨_, h₁⟩, ⟨_, h₂⟩ => le
t ⟨f, hf⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.schroeder_bernstein`：schroeder_bernstein {f : α -> β}
 {g : β -> α} (hf : Function.Injective f) (hg : Function.Injective g) : exists h
 : α -> β, Bijective h

--- 原说明 ---
**The Schröder-Bernstein Theorem**: Given embeddings `α ↪ β` and `β ↪ α`, there 
exists an
equivalence `α ≃ β`.
-/
theorem antisymm : (α ↪ β) → (β ↪ α) → Nonempty (α ≃ β)
  | ⟨_, h₁⟩, ⟨_, h₂⟩ =>
    let ⟨f, hf⟩ := schroeder_bernstein h₁ h₂
    ⟨Equiv.ofBijective f hf⟩

end antisymm

section Wo

variable {ι : Type u} (β : ι → Type v)

/-- `sets β` -/
/-
**Function.Embedding.sets** 是 Mathlib 中的一个缩写定义，位于命名空间 `Function.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sets β`
-/
private abbrev sets :=
  { s : Set (∀ i, β i) | ∀ i : ι, s.InjOn fun x => x i }

/-- The cardinals are well-ordered. We express it here by the fact that in any set of cardinals
there is an element that injects into the others.
See `Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice instances. -/
/-
**Function.Embedding.min_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding
`。
形式化陈述：min_injective [I : Nonempty ι] : exists i, Nonempty (forall j, β i ↪ β j)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_subset`：zorn_subset (S : Set (Set α)) (h : forall c subseteq S, IsC
hain (· subseteq ·) c -> exists ub in S, forall s in c, s subseteq ub) : exists 
m…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `Classical.by_contradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Classical.axiom_of_choice`：∀ {α : Sort u} {β : α → Sort v} {r : (x : α) 
→ β x → Prop}, (∀ (x : α), ∃ y, r x y) → ∃ f, ∀ (x : α), r x (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Maximal.eq_of_subset`：Maximal.eq_of_subset (h : Maximal P s) (ht : P t) 
(hst : s subseteq t) : s = t
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Set.InjOn.injective`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α 
→ β}, Set.InjOn f s → Function.Injective (s.domRestrict f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)

--- 原说明 ---
The cardinals are well-ordered. We express it here by the fact that in any set o
f cardinals
there is an element that injects into the others.
See `Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice inst
ances.
-/
theorem min_injective [I : Nonempty ι] : ∃ i, Nonempty (∀ j, β i ↪ β j) :=
  let ⟨s, hs⟩ := show ∃ s, Maximal (· ∈ sets β) s by
    refine zorn_subset _ fun c hc hcc ↦
      ⟨⋃₀ c, fun i x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ hi ↦ ?_, fun _ ↦ subset_sUnion_of_mem⟩
    exact (hcc.total hpc hqc).elim (fun h ↦ hc hqc i (h hxp) hyq hi)
      fun h ↦ hc hpc i hxp (h hyq) hi
  let ⟨i, e⟩ :=
    show ∃ i, Surjective fun x : s => x.val i from
      Classical.by_contradiction fun h =>
        have h : ∀ i, ∃ y, ∀ x ∈ s, (x : ∀ i, β i) i ≠ y := by
          simpa [Surjective] using h
        let ⟨f, hf⟩ := Classical.axiom_of_choice h
        have : f ∈ s :=
          have : insert f s ∈ sets β := fun i x hx y hy => by
            rcases hx with hx | hx <;> rcases hy with hy | hy; · simp [hx, hy]
            · subst x
              exact fun e => (hf i y hy e.symm).elim
            · subst y
              exact fun e => (hf i x hx e).elim
            · exact hs.prop i hx hy
          hs.eq_of_subset this (subset_insert _ _) ▸ mem_insert ..
        let ⟨i⟩ := I
        hf i f this rfl
  ⟨i, ⟨fun j => ⟨s.domRestrict (fun x => x j) ∘ surjInv e,
    ((hs.1 j).injective).comp (injective_surjInv _)⟩⟩⟩

end Wo

/-- The cardinals are totally ordered. See
`Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice
instance. -/
/-
**Function.Embedding.total** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：total (α : Type u) (β : Type v) : Nonempty (α ↪ β) ∨ Nonempty (β ↪ α)
参数：α : Type u；β : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.min_injective`：min_injective [I : Nonempty ι] : exist
s i, Nonempty (forall j, β i ↪ β j)

--- 原说明 ---
The cardinals are totally ordered. See
`Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice
instance.
-/
theorem total (α : Type u) (β : Type v) : Nonempty (α ↪ β) ∨ Nonempty (β ↪ α) :=
  match @min_injective Bool (fun b => cond b (ULift α) (ULift.{max u v, v} β)) ⟨true⟩
    with
  | ⟨true, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h false
    Or.inl ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩
  | ⟨false, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h true
    Or.inr ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩

end Embedding

end Function

