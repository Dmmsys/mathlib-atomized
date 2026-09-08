/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# (Co)induced representations of a finite index subgroup

Given a commutative ring `k`, a finite index subgroup `S ≤ G`, and a `k`-linear `S`-representation
`A`, this file defines an isomorphism $Ind_S^G(A) ≅ Coind_S^G(A)$. Given `g : G` and `a : A`, the
forward map sends `⟦g ⊗ₜ[k] a⟧` to the function `G → A` supported at `sg` by `ρ(s)(a)` for `s : S`
and which is 0 elsewhere. Meanwhile, the inverse sends `f : G → A` to `∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for
`1 ≤ i ≤ n`, where `g₁, ..., gₙ` is a set of right coset representatives of `S`.

## Main definitions

* `Rep.indCoindIso A`: An isomorphism `Ind_S^G(A) ≅ Coind_S^G(A)` for a finite index subgroup
  `S ≤ G` and a `k`-linear `S`-representation `A`.
* `Rep.indCoindNatIso k S`: A natural isomorphism between the functors `Ind_S^G` and `Coind_S^G`.

TODO : Fix the universe constraint
-/

@[expose] public section

universe t w u u' v v'

namespace Rep

open CategoryTheory Finsupp TensorProduct Representation

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel (QuotientGroup.rightRel S)] (A : Rep.{w} k S)

/-- Let `S ≤ G` be a subgroup and `(A, ρ)` a `k`-linear `S`-representation. Then given `g : G` and
`a : A`, this is the function `G → A` sending `sg` to `ρ(s)(a)` for all `s : S` and everything else
to 0. -/
/-
**Rep.indToCoindAux** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：indToCoindAux (g : G) : A ->ₗ[k] (G -> A)
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S ≤ G` be a subgroup and `(A, ρ)` a `k`-linear `S`-representation. Then giv
en `g : G` and
`a : A`, this is the function `G → A` sending `sg` to `ρ(s)(a)` for all `s : S` 
and everything else
to 0.
-/
noncomputable def indToCoindAux (g : G) : A →ₗ[k] (G → A) :=
  LinearMap.pi (fun g₁ => if h : (QuotientGroup.rightRel S).r g₁ g then
    A.ρ ⟨g₁ * g⁻¹, by rcases h with ⟨s, rfl⟩; exact mul_inv_cancel_right s.1 g ▸ s.2⟩ else 0)

variable {A}

@[simp]
/-
**Rep.indToCoindAux_self** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：indToCoindAux_self (g : G) (a : A) : indToCoindAux A g a g = a
参数：g : G；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rep.indToCoindAux.eq_1`：∀ {k : Type u} {G : Type v} [inst : CommRing k] 
[inst_1 : Group G] {S : Subgroup G}   [inst_2 : DecidableRel ⇑(QuotientGroup.rig
htRel S)] (A…
· 使用定理 `LinearMap.pi_apply`：pi_apply (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c : M₂) (i 
: ι) : pi f c i = f i c
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma indToCoindAux_self (g : G) (a : A) :
    indToCoindAux A g a g = a := by
  rw [indToCoindAux, LinearMap.pi_apply, dif_pos]
  · simp [← S.1.one_def]
  · rfl
/-
**Rep.indToCoindAux_of_not_rel** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：indToCoindAux_of_not_rel (g g₁ : G) (a : A) (h : ¬(QuotientGroup.rightRel 
S).r g₁ g) : indToCoindAux A g a g₁ = 0
参数：g g₁ : G；a : A；h : ¬(QuotientGroup.rightRel S).r g₁ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma indToCoindAux_of_not_rel (g g₁ : G) (a : A) (h : ¬(QuotientGroup.rightRel S).r g₁ g) :
    indToCoindAux A g a g₁ = 0 := by
  simp [indToCoindAux, dif_neg h]

@[simp]
/-
**Rep.indToCoindAux_mul_snd** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：indToCoindAux_mul_snd (g g₁ : G) (a : A) (s : S) : indToCoindAux A g a (s 
* g₁) = A.ρ s (indToCoindAux A g a g₁)
参数：g g₁ : G；a : A；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Rep.indToCoindAux_of_not_rel`：indToCoindAux_of_not_rel (g g₁ : G) (a : A
) (h : ¬(QuotientGroup.rightRel S).r g₁ g) : indToCoindAux A g a g₁ = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
lemma indToCoindAux_mul_snd (g g₁ : G) (a : A) (s : S) :
    indToCoindAux A g a (s * g₁) = A.ρ s (indToCoindAux A g a g₁) := by
  rcases em ((QuotientGroup.rightRel S).r g₁ g) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s * s₁, mul_assoc ..⟩, dif_pos ⟨s₁, rfl⟩]
    simp [S.1.smul_def, mul_assoc, ← S.1.mul_def]
  · rw [indToCoindAux_of_not_rel _ _ _ h, indToCoindAux_of_not_rel, map_zero]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s⁻¹ * s₁, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]
/-
**Rep.indToCoindAux_mul_fst** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：indToCoindAux_mul_fst (g₁ g₂ : G) (a : A) (s : S) : indToCoindAux A (s * g
₁) (A.ρ s a) g₂ = indToCoindAux A g₁ a g₂
参数：g₁ g₂ : G；a : A；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `Rep.indToCoindAux_of_not_rel`：indToCoindAux_of_not_rel (g g₁ : G) (a : A
) (h : ¬(QuotientGroup.rightRel S).r g₁ g) : indToCoindAux A g a g₁ = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
lemma indToCoindAux_mul_fst (g₁ g₂ : G) (a : A) (s : S) :
     indToCoindAux A (s * g₁) (A.ρ s a) g₂ = indToCoindAux A g₁ a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s₁ * s⁻¹, by simp [S.1.smul_def, smul_eq_mul, mul_assoc]⟩, dif_pos ⟨s₁, rfl⟩,
      ← Module.End.mul_apply, ← map_mul]
    congr
    simp [Subtype.ext_iff, S.1.smul_def, mul_assoc]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s₁ * s, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]
/-
**Rep.indToCoindAux_snd_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：indToCoindAux_snd_mul_inv (g₁ g₂ g₃ : G) (a : A) : indToCoindAux A g₁ a (g
₂ * g₃⁻¹) = indToCoindAux A (g₁ * g₃) a g₂
参数：g₁ g₂ g₃ : G；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Rep.indToCoindAux_mul_snd`：indToCoindAux_mul_snd (g g₁ : G) (a : A) (s :
 S) : indToCoindAux A g a (s * g₁) = A.ρ s (indToCoindAux A g a g₁)
· 使用引理 `Rep.indToCoindAux_self`：indToCoindAux_self (g : G) (a : A) : indToCoindA
ux A g a g = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Rep.indToCoindAux_of_not_rel`：indToCoindAux_of_not_rel (g g₁ : G) (a : A
) (h : ¬(QuotientGroup.rightRel S).r g₁ g) : indToCoindAux A g a g₁ = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
lemma indToCoindAux_snd_mul_inv (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux A g₁ a (g₂ * g₃⁻¹) = indToCoindAux A (g₁ * g₃) a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r (g₂ * g₃⁻¹) g₁) with ⟨s, hs⟩ | h
  · simp [S.1.smul_def, mul_assoc, ← eq_mul_inv_iff_mul_eq.1 hs]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s, hs⟩ => ⟨s, by simpa [S.1.smul_def, eq_mul_inv_iff_mul_eq, mul_assoc]⟩) h

@[simp]
/-
**Rep.indToCoindAux_fst_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：indToCoindAux_fst_mul_inv (g₁ g₂ g₃ : G) (a : A) : indToCoindAux A (g₁ * g
₂⁻¹) a g₃ = indToCoindAux A g₁ a (g₃ * g₂)
参数：g₁ g₂ g₃ : G；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rep.indToCoindAux_snd_mul_inv`：indToCoindAux_snd_mul_inv (g₁ g₂ g₃ : G) 
(a : A) : indToCoindAux A g₁ a (g₂ * g₃⁻¹) = indToCoindAux A (g₁ * g₃) a g₂
-/
lemma indToCoindAux_fst_mul_inv (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux A (g₁ * g₂⁻¹) a g₃ = indToCoindAux A g₁ a (g₃ * g₂) := by
  simpa using (indToCoindAux_snd_mul_inv g₁ g₃ g₂⁻¹ a).symm
/-
**Rep.indToCoindAux_comm** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：indToCoindAux_comm {A B : Rep k S} (f : A ⟶ B) (g₁ g₂ : G) (a : A) : indTo
CoindAux B g₁ (f.hom a) g₂ = f.hom (indToCoindAux A g₁ a g₂)
参数：f : A ⟶ B；g₁ g₂ : G；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用引理 `Rep.indToCoindAux_mul_snd`：indToCoindAux_mul_snd (g g₁ : G) (a : A) (s :
 S) : indToCoindAux A g a (s * g₁) = A.ρ s (indToCoindAux A g a g₁)
· 使用引理 `Rep.indToCoindAux_self`：indToCoindAux_self (g : G) (a : A) : indToCoindA
ux A g a g = a
· 使用引理 `Rep.hom_comm_apply`：hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (
A.ρ g a) = B.ρ g (f.hom a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Rep.indToCoindAux_of_not_rel`：indToCoindAux_of_not_rel (g g₁ : G) (a : A
) (h : ¬(QuotientGroup.rightRel S).r g₁ g) : indToCoindAux A g a g₁ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Representation.IntertwiningMap.instLinearMapClass`：∀ {A : Type u_1} {G :
 Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]
   [inst_2 : AddCommMonoid V] [inst_3 :…
-/
lemma indToCoindAux_comm {A B : Rep k S} (f : A ⟶ B) (g₁ g₂ : G) (a : A) :
    indToCoindAux B g₁ (f.hom a) g₂ = f.hom (indToCoindAux A g₁ a g₂) := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s, rfl⟩ | h
  · simp [S.1.smul_def, hom_comm_apply]
  · simp [indToCoindAux_of_not_rel (h := h)]

set_option backward.isDefEq.respectTransparency.types false in
variable (A) in
/-- Let `S ≤ G` be a subgroup and `A` a `k`-linear `S`-representation. This is the `k`-linear map
`Ind_S^G(A) →ₗ[k] Coind_S^G(A)` sending `(⟦g ⊗ₜ[k] a⟧, sg) ↦ ρ(s)(a)`. -/
/-
**Rep.indToCoind** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：indToCoind : ind S.subtype A ->ₗ[k] coind S.subtype A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S ≤ G` be a subgroup and `A` a `k`-linear `S`-representation. This is the `
k`-linear map
`Ind_S^G(A) →ₗ[k] Coind_S^G(A)` sending `(⟦g ⊗ₜ[k] a⟧, sg) ↦ ρ(s)(a)`.
-/
noncomputable abbrev indToCoind :
    ind S.subtype A →ₗ[k] coind S.subtype A :=
  Representation.Coinvariants.lift _ (TensorProduct.lift <| (linearCombination _ fun g =>
    LinearMap.codRestrict _ (indToCoindAux A g) fun _ _ _ => by simp) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun _ => by ext; simp

variable [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (A) in
/-- Let `S ≤ G` be a finite index subgroup, `g₁, ..., gₙ` a set of right coset representatives of
`S`, and `A` a `k`-linear `S`-representation. This is the `k`-linear map
`Coind_S^G(A) →ₗ[k] Ind_S^G(A)` sending `f : G → A` to `∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for `1 ≤ i ≤ n`. -/
@[simps]
/-
**Rep.coindToInd** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coindToInd : coind S.subtype A ->ₗ[k] ind S.subtype A where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S ≤ G` be a finite index subgroup, `g₁, ..., gₙ` a set of right coset repre
sentatives of
`S`, and `A` a `k`-linear `S`-representation. This is the `k`-linear map
`Coind_S^G(A) →ₗ[k] Ind_S^G(A)` sending `f : G → A` to `∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for
 `1 ≤ i ≤ n`.
-/
noncomputable def coindToInd : coind S.subtype A →ₗ[k] ind S.subtype A where
  toFun f := ∑ g : Quotient (QuotientGroup.rightRel S), Quotient.liftOn g (fun g =>
    IndV.mk S.subtype _ g (f.1 g)) fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
      (Submodule.Quotient.eq _).2 <| Coinvariants.mem_ker_of_eq s
        (.single g₂ 1 ⊗ₜ[k] f.1 g₂) _ <| by have := f.2 s g₂; simp_all
  map_add' _ _ := by simpa [← Finset.sum_add_distrib, TensorProduct.tmul_add] using
      Finset.sum_congr rfl fun z _ => Quotient.inductionOn z fun _ => by simp
  map_smul' _ _ := by simpa [Finset.smul_sum] using Finset.sum_congr rfl fun z _ =>
    Quotient.inductionOn z fun _ => by simp

omit [DecidableRel (QuotientGroup.rightRel S)] in
/-
**Rep.coindToInd_of_support_subset_orbit** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：coindToInd_of_support_subset_orbit (g : G) (f : coind S.subtype A) (hx : f
.1.support subseteq MulAction.orbit S g) : coindToInd A f = IndV.mk S.subtype _ 
g (f.1 g)
参数：g : G；f : coind S.subtype A；hx : f.1.support subseteq MulAction.orbit S g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rep.coindToInd_apply`：∀ {k : Type u} {G : Type v} [inst : CommRing k] [i
nst_1 : Group G] {S : Subgroup G} (A : Rep.{w, u, v} k ↥S)   [inst_2 : S.FiniteI
ndex] (f :…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma coindToInd_of_support_subset_orbit (g : G) (f : coind S.subtype A)
    (hx : f.1.support ⊆ MulAction.orbit S g) :
    coindToInd A f = IndV.mk S.subtype _ g (f.1 g) := by
  rw [coindToInd_apply, Finset.sum_eq_single ⟦g⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    have : f.1 b = 0 := by
      simp_all only [Function.support_subset_iff, ne_eq, Quotient.eq]
      contrapose! hx
      use b, hx, hb
    simp_all
  · simp

variable (A)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Rep.coindToInd_indToCoind** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：coindToInd_indToCoind : A.indToCoind ∘ₗ A.coindToInd = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rep.coindToInd_apply`：∀ {k : Type u} {G : Type v} [inst : CommRing k] [i
nst_1 : Group G] {S : Subgroup G} (A : Rep.{w, u, v} k ↥S)   [inst_2 : S.FiniteI
ndex] (f :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddSubmonoidClass.coe_finsetSum`：∀ {B : Type u_3} {S : B} {ι : Type u_4}
 {M : Type u_5} [inst : AddCommMonoid M] [inst_1 : SetLike B M]   [inst_2 : AddS
ubmonoidClass B M] (f…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Rep.indToCoindAux_of_not_rel`：indToCoindAux_of_not_rel (g g₁ : G) (a : A
) (h : ¬(QuotientGroup.rightRel S).r g₁ g) : indToCoindAux A g a g₁ = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用引理 `Rep.indToCoindAux_self`：indToCoindAux_self (g : G) (a : A) : indToCoindA
ux A g a g = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coindToInd_indToCoind : A.indToCoind ∘ₗ A.coindToInd = LinearMap.id := by
  ext g a
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  conv_lhs => rw [coindToInd_apply]
  simp only [map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single ⟦a⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    simpa using indToCoindAux_of_not_rel b a (g.1 b) (mt Quotient.sound hb.symm)
  · simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**Rep.indToCoind_coindToInd** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：indToCoind_coindToInd : A.coindToInd ∘ₗ A.indToCoind = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.Coinvariants.hom_ext`：hom_ext {f g : Coinvariants ρ ->ₗ[k
] W} (H : f ∘ₗ mk ρ = g ∘ₗ mk ρ) : f = g
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MonoidAlgebra.lhom_ext'`：lhom_ext' {N : Type*} [Semiring R] [AddCommMono
id N] [Module R N] [Module R S] ⦃f g : S[M] ->ₗ[R] N⦄ (H : forall (x : M), Linea
rMap.comp f (…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `Rep.coindToInd_of_support_subset_orbit`：coindToInd_of_support_subset_orb
it (g : G) (f : coind S.subtype A) (hx : f.1.support subseteq MulAction.orbit S 
g) : coindToInd A f = IndV.m…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Rep.indToCoindAux_of_not_rel`：indToCoindAux_of_not_rel (g g₁ : G) (a : A
) (h : ¬(QuotientGroup.rightRel S).r g₁ g) : indToCoindAux A g a g₁ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Rep.indToCoindAux_self`：indToCoindAux_self (g : G) (a : A) : indToCoindA
ux A g a g = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma indToCoind_coindToInd : A.coindToInd ∘ₗ A.indToCoind = LinearMap.id := by
  ext g a
  simp only [LinearMap.comp_apply, AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.id_apply]
  rw [coindToInd_of_support_subset_orbit g]
  · simp
  · intro x hx
    contrapose hx
    simpa using indToCoindAux_of_not_rel g x a hx

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `S ≤ G` be a finite index subgroup, `g₁, ..., gₙ` a set of right coset representatives of
`S`, and `A` a `k`-linear `S`-representation. This is an isomorphism `Ind_S^G(A) ≅ Coind_S^G(A)`.
The forward map sends `(⟦g ⊗ₜ[k] a⟧, sg) ↦ ρ(s)(a)`, and the inverse sends `f : G → A` to
`∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for `1 ≤ i ≤ n`. -/
@[simps! hom_hom_toLinearMap inv_hom_toLinearMap]
/-
**Rep.indCoindIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：indCoindIso (A : Rep.{max w u} k S) : ind S.subtype A ≅ coind S.subtype A
参数：A : Rep.{max w u} k S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Rep.coindToInd_indToCoind`：coindToInd_indToCoind : A.indToCoind ∘ₗ A.coi
ndToInd = LinearMap.id
· 使用引理 `Rep.indToCoind_coindToInd`：indToCoind_coindToInd : A.coindToInd ∘ₗ A.ind
ToCoind = LinearMap.id

--- 原说明 ---
Let `S ≤ G` be a finite index subgroup, `g₁, ..., gₙ` a set of right coset repre
sentatives of
`S`, and `A` a `k`-linear `S`-representation. This is an isomorphism `Ind_S^G(A)
 ≅ Coind_S^G(A)`.
The forward map sends `(⟦g ⊗ₜ[k] a⟧, sg) ↦ ρ(s)(a)`, and the inverse sends `f : 
G → A` to
`∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for `1 ≤ i ≤ n`.
-/
noncomputable def indCoindIso (A : Rep.{max w u} k S) :
    ind S.subtype A ≅ coind S.subtype A :=
  mkIso (.mk (.ofLinearMap (indToCoind A) (coindToInd A)
    (coindToInd_indToCoind A) (indToCoind_coindToInd A)) <| fun g ↦ by ext; simp)

variable (k S)

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a finite index subgroup `S ≤ G`, this is a natural isomorphism between the `Ind_S^G` and
`Coind_G^S` functors `Rep k S ⥤ Rep k G`. -/
@[implicit_reducible, simps! hom_app inv_app]
/-
**Rep.indCoindNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：indCoindNatIso : indFunctor k S.subtype ≅ coindFunctor.{max w u} k S.subty
pe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite index subgroup `S ≤ G`, this is a natural isomorphism between the
 `Ind_S^G` and
`Coind_G^S` functors `Rep k S ⥤ Rep k G`.
-/
noncomputable def indCoindNatIso :
    indFunctor k S.subtype ≅ coindFunctor.{max w u} k S.subtype :=
  NatIso.ofComponents (fun (A : Rep k S) => indCoindIso A) fun f => by
    simp only [indFunctor_obj, coindFunctor_obj];
    ext g1 x g2
    simp [indToCoind, indMap, indToCoindAux_comm]

/-- Given a finite index subgroup `S ≤ G`, `Ind_S^G` is right adjoint to the restriction functor
`Res k G ⥤ Res k S`, since it is naturally isomorphic to `Coind_S^G`. -/
/-
**Rep.resIndAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：resIndAdjunction : resFunctor.{max w u v} S.subtype ⊣ indFunctor.{max w u 
v} k S.subtype
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite index subgroup `S ≤ G`, `Ind_S^G` is right adjoint to the restric
tion functor
`Res k G ⥤ Res k S`, since it is naturally isomorphic to `Coind_S^G`.
-/
noncomputable def resIndAdjunction :
    resFunctor.{max w u v} S.subtype ⊣ indFunctor.{max w u v} k S.subtype :=
  (resCoindAdjunction.{max w u v} k S.subtype).ofNatIsoRight (indCoindNatIso.{max w u v} k S).symm

omit [DecidableRel (QuotientGroup.rightRel S)] in
@[instance] -- Note: we must use `@[instance] theorem` here due to [lean4#5595](https://github.com/leanprover/lean4/issues/5595).
/-
**Rep.instIsRightAdjointSubtypeMemSubgroupIndFunctorSubtype** 是 Mathlib 中的一个定理，位
于命名空间 `Rep`。
形式化陈述：instIsRightAdjointSubtypeMemSubgroupIndFunctorSubtype : (indFunctor.{max w
 u v} k S.subtype).IsRightAdjoint
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.isRightAdjoint`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
-/
theorem instIsRightAdjointSubtypeMemSubgroupIndFunctorSubtype :
    (indFunctor.{max w u v} k S.subtype).IsRightAdjoint :=
  open scoped Classical in (resIndAdjunction k S).isRightAdjoint

variable {k S}

@[simp]
/-
**Rep.resIndAdjunction_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：resIndAdjunction_counit_app (A : Rep.{max w u v} k S) : (resIndAdjunction.
{w, u, v} k S).counit.app A = (resFunctor S.subtype).map (indCoindIso.{max w (ma
x u v)} A).hom ≫ (resCoindAdjunction.{max w u} k S.subtype).counit.app A
参数：A : Rep.{max w u v} k S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resIndAdjunction_counit_app (A : Rep.{max w u v} k S) :
    (resIndAdjunction.{w, u, v} k S).counit.app A =
      (resFunctor S.subtype).map (indCoindIso.{max w (max u v)} A).hom ≫
      (resCoindAdjunction.{max w u} k S.subtype).counit.app A := rfl

@[simp]
/-
**Rep.resIndAdjunction_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：resIndAdjunction_unit_app (B : Rep.{max w u v} k G) : (resIndAdjunction.{w
, u, v} k S).unit.app B = (resCoindAdjunction.{max w u} k S.subtype).unit.app B 
≫ (indCoindIso.{max w (max u v)} (res S.subtype B)).inv
参数：B : Rep.{max w u v} k G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resIndAdjunction_unit_app (B : Rep.{max w u v} k G) :
    (resIndAdjunction.{w, u, v} k S).unit.app B =
      (resCoindAdjunction.{max w u} k S.subtype).unit.app B ≫
      (indCoindIso.{max w (max u v)} (res S.subtype B)).inv := rfl
/-
**Rep.resIndAdjunction_homEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：resIndAdjunction_homEquiv_apply (A : Rep.{max w u v} k S) {B : Rep.{max w 
u v} k G} (f : res S.subtype B ⟶ A) : (resIndAdjunction.{w, u, v} k S).homEquiv 
_ _ f = resCoindHomEquiv.{max w u v} S.subtype B A f ≫ (indCoindIso.{max w u v} 
A).inv
参数：A : Rep.{max w u v} k S；f : res S.subtype B ⟶ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rep.resIndAdjunction.eq_1`：∀ (k : Type u) {G : Type v} [inst : CommRing 
k] [inst_1 : Group G] (S : Subgroup G)   [inst_2 : DecidableRel ⇑(QuotientGroup.
rightRel S)] [i…
· 使用引理 `CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_apply`：homEquiv_ofNatIs
oRight_apply {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) {X : C} {Y : 
D} (f : F.obj X ⟶ Y) : (ofNatIsoRight adj is…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma resIndAdjunction_homEquiv_apply (A : Rep.{max w u v} k S)
    {B : Rep.{max w u v} k G} (f : res S.subtype B ⟶ A) :
    (resIndAdjunction.{w, u, v} k S).homEquiv _ _ f =
      resCoindHomEquiv.{max w u v} S.subtype B A f ≫ (indCoindIso.{max w u v} A).inv := by
  rw [resIndAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply]
  simp [resCoindHomEquiv]
/-
**Rep.resIndAdjunction_homEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：resIndAdjunction_homEquiv_symm_apply (A : Rep.{max w u v} k S) {B : Rep.{m
ax w u v} k G} (f : B ⟶ (indFunctor k S.subtype).obj A) : ((resIndAdjunction k S
).homEquiv _ _).symm f = (resCoindHomEquiv.{max w u v} S.subtype B A).symm (f ≫ 
(indCoindIso.{max w u v} A).hom)
参数：A : Rep.{max w u v} k S；f : B ⟶ (indFunctor k S.subtype).obj A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma resIndAdjunction_homEquiv_symm_apply (A : Rep.{max w u v} k S)
    {B : Rep.{max w u v} k G}
    (f : B ⟶ (indFunctor k S.subtype).obj A) :
    ((resIndAdjunction k S).homEquiv _ _).symm f =
      (resCoindHomEquiv.{max w u v} S.subtype B A).symm (f ≫ (indCoindIso.{max w u v} A).hom) :=
  rfl

variable (k S) in
/-- Given a finite index subgroup `S ≤ G`, `Coind_S^G` is left adjoint to the restriction functor
`Res k G ⥤ Res k S`, since it is naturally isomorphic to `Ind_S^G`. -/
/-
**Rep.coindResAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coindResAdjunction : coindFunctor k S.subtype ⊣ resFunctor.{max w u v} S.s
ubtype
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite index subgroup `S ≤ G`, `Coind_S^G` is left adjoint to the restri
ction functor
`Res k G ⥤ Res k S`, since it is naturally isomorphic to `Ind_S^G`.
-/
noncomputable def coindResAdjunction :
    coindFunctor k S.subtype ⊣ resFunctor.{max w u v} S.subtype :=
  (indResAdjunction k S.subtype).ofNatIsoLeft (indCoindNatIso.{max w u v} k S)

omit [DecidableRel (QuotientGroup.rightRel S)] in
@[instance] -- Note: we must use `@[instance] theorem` here due to [lean4#5595](https://github.com/leanprover/lean4/issues/5595).
/-
**Rep.instIsLeftAdjointSubtypeMemSubgroupCoindFunctorSubtype** 是 Mathlib 中的一个定理，
位于命名空间 `Rep`。
形式化陈述：instIsLeftAdjointSubtypeMemSubgroupCoindFunctorSubtype : (coindFunctor.{ma
x w u v} k S.subtype).IsLeftAdjoint
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isLeftAdjoint`：isLeftAdjoint (adj : F ⊣ G) : F
.IsLeftAdjoint
-/
theorem instIsLeftAdjointSubtypeMemSubgroupCoindFunctorSubtype :
    (coindFunctor.{max w u v} k S.subtype).IsLeftAdjoint :=
  open scoped Classical in (coindResAdjunction k S).isLeftAdjoint

@[simp]
/-
**Rep.coindResAdjunction_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：coindResAdjunction_counit_app (B : Rep.{max w u v} k G) : (coindResAdjunct
ion.{w, u, v} k S).counit.app B = (indCoindIso.{max w u v} (res S.subtype B)).in
v ≫ (indResAdjunction k S.subtype).counit.app B
参数：B : Rep.{max w u v} k G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coindResAdjunction_counit_app (B : Rep.{max w u v} k G) :
    (coindResAdjunction.{w, u, v} k S).counit.app B =
      (indCoindIso.{max w u v} (res S.subtype B)).inv ≫
      (indResAdjunction k S.subtype).counit.app B :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Rep.coindResAdjunction_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：coindResAdjunction_unit_app (A : Rep.{max w u v} k S) : (coindResAdjunctio
n k S).unit.app A = (indResAdjunction k S.subtype).unit.app A ≫ (resFunctor S.su
btype).map (indCoindIso.{max w u v} A).hom
参数：A : Rep.{max w u v} k S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Adjunction.ofNatIsoLeft_unit`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Rep.indCoindIso_hom_hom_toLinearMap`：∀ {k : Type u} {G : Type v} [inst :
 CommRing k] [inst_1 : Group G] {S : Subgroup G}   [inst_2 : DecidableRel ⇑(Quot
ientGroup.rightRel S)] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coindResAdjunction_unit_app (A : Rep.{max w u v} k S) :
    (coindResAdjunction k S).unit.app A = (indResAdjunction k S.subtype).unit.app A ≫
      (resFunctor S.subtype).map (indCoindIso.{max w u v} A).hom := by
  ext
  simp [coindResAdjunction]
/-
**Rep.coindResAdjunction_homEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：coindResAdjunction_homEquiv_apply (A : Rep.{max w u v} k S) {B : Rep k G} 
(f : coind S.subtype A ⟶ B) : (coindResAdjunction k S).homEquiv _ _ f = indResHo
mEquiv S.subtype A B ((indCoindIso.{max w u v} A).hom ≫ f)
参数：A : Rep.{max w u v} k S；f : coind S.subtype A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coindResAdjunction_homEquiv_apply (A : Rep.{max w u v} k S)
    {B : Rep k G} (f : coind S.subtype A ⟶ B) :
    (coindResAdjunction k S).homEquiv _ _ f =
      indResHomEquiv S.subtype A B ((indCoindIso.{max w u v} A).hom ≫ f) := by
  rfl
/-
**Rep.coindResAdjunction_homEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：coindResAdjunction_homEquiv_symm_apply (A : Rep.{max w u v} k S) {B : Rep 
k G} (f : A ⟶ res S.subtype B) : ((coindResAdjunction.{max w u v} k S).homEquiv 
_ _).symm f = (indCoindIso.{max w u v} A).inv ≫ (indResHomEquiv S.subtype A B).s
ymm f
参数：A : Rep.{max w u v} k S；f : A ⟶ res S.subtype B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_symm_apply`：homEquiv_ofN
atIsoLeft_symm_apply {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) {X : 
C} {Y : D} (f : X ⟶ H.obj Y) : ((ofNatIsoLeft ad…
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coindResAdjunction_homEquiv_symm_apply (A : Rep.{max w u v} k S)
    {B : Rep k G} (f : A ⟶ res S.subtype B) :
    ((coindResAdjunction.{max w u v} k S).homEquiv _ _).symm f =
      (indCoindIso.{max w u v} A).inv ≫ (indResHomEquiv S.subtype A B).symm f := by
  simp [coindResAdjunction, indResHomEquiv, indResAdjunction,
    Adjunction.homEquiv_ofNatIsoLeft_symm_apply _]

end Rep

