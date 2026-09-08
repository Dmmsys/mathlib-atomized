/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals in product rings

For commutative rings `R` and `S` and ideals `I ≤ R`, `J ≤ S`, we define `Ideal.prod I J` as the
product `I × J`, viewed as an ideal of `R × S`. In `ideal_prod_eq` we show that every ideal of
`R × S` is of this form.  Furthermore, we show that every prime ideal of `R × S` is of the form
`p × S` or `R × p`, where `p` is a prime ideal.
-/

@[expose] public section


universe u v

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S] (I : Ideal R) (J : Ideal S)

namespace Ideal

/-- `I × J` as an ideal of `R × S`. -/
/-
**Ideal.prod** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：prod : Ideal (R × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`I × J` as an ideal of `R × S`.
-/
def prod : Ideal (R × S) := I.comap (RingHom.fst R S) ⊓ J.comap (RingHom.snd R S)

@[simp]
/-
**Ideal.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：coe_prod (I : Ideal R) (J : Ideal S) : ↑(prod I J) = (I ×ˢ J : Set (R × S)
)
参数：I : Ideal R；J : Ideal S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (I : Ideal R) (J : Ideal S) : ↑(prod I J) = (I ×ˢ J : Set (R × S)) :=
  rfl

@[simp]
/-
**Ideal.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_prod {x : R × S} : x in prod I J ↔ x.1 in I ∧ x.2 in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {x : R × S} : x ∈ prod I J ↔ x.1 ∈ I ∧ x.2 ∈ J :=
  Iff.rfl

@[simp]
/-
**Ideal._root_.RingHom.ker_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RingHom.ker_prodMap {T U : Type*} [Semiring T] [Semiring U] (f : R →+* S)
    (g : T →+* U) : RingHom.ker (f.prodMap g) = (RingHom.ker f).prod (RingHom.ker g) := by
  ext ⟨⟩; simp

@[simp]
/-
**Ideal.prod_top_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_top_top : prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_top_top : prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤ :=
  Ideal.ext <| by simp

@[simp]
/-
**Ideal.prod_bot_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_bot_bot : prod (⊥ : Ideal R) (⊥ : Ideal S) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
-/
theorem prod_bot_bot : prod (⊥ : Ideal R) (⊥ : Ideal S) = ⊥ :=
  SetLike.coe_injective <| Set.singleton_prod_singleton

@[gcongr]
/-
**Ideal.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_mono {I₁ I₂ : Ideal R} {J₁ J₂ : Ideal S} (hI : I₁ <= I₂) (hJ : J₁ <= 
J₂) : prod I₁ J₁ <= prod I₂ J₂
参数：hI : I₁ <= I₂；hJ : J₁ <= J₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono {I₁ I₂ : Ideal R} {J₁ J₂ : Ideal S} (hI : I₁ ≤ I₂) (hJ : J₁ ≤ J₂) :
    prod I₁ J₁ ≤ prod I₂ J₂ :=
  Set.prod_mono hI hJ
/-
**Ideal.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_mono_left {I₁ I₂ : Ideal R} {J : Ideal S} (hI : I₁ <= I₂) : prod I₁ J
 <= prod I₂ J
参数：hI : I₁ <= I₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono_left`：prod_mono_left (hs : s₁ subseteq s₂) : s₁ ×ˢ t subse
teq s₂ ×ˢ t
-/
theorem prod_mono_left {I₁ I₂ : Ideal R} {J : Ideal S} (hI : I₁ ≤ I₂) : prod I₁ J ≤ prod I₂ J :=
  Set.prod_mono_left hI
/-
**Ideal.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_mono_right {I : Ideal R} {J₁ J₂ : Ideal S} (hJ : J₁ <= J₂) : prod I J
₁ <= prod I J₂
参数：hJ : J₁ <= J₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono_right`：prod_mono_right (ht : t₁ subseteq t₂) : s ×ˢ t₁ sub
seteq s ×ˢ t₂
-/
theorem prod_mono_right {I : Ideal R} {J₁ J₂ : Ideal S} (hJ : J₁ ≤ J₂) : prod I J₁ ≤ prod I J₂ :=
  Set.prod_mono_right hJ

/-- Every ideal of the product ring is of the form `I × J`, where `I` and `J` can be explicitly
    given as the image under the projection maps. -/
/-
**Ideal.ideal_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ideal_prod_eq (I : Ideal (R × S)) : I = Ideal.prod (map (RingHom.fst R S) 
I : Ideal R) (map (RingHom.snd R S) I)
参数：I : Ideal (R × S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_prod`：mem_prod {x : R × S} : x in prod I J ↔ x.1 in I ∧ x.2 in
 J
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I

--- 原说明 ---
Every ideal of the product ring is of the form `I × J`, where `I` and `J` can be
 explicitly
    given as the image under the projection maps.
-/
theorem ideal_prod_eq (I : Ideal (R × S)) :
    I = Ideal.prod (map (RingHom.fst R S) I : Ideal R) (map (RingHom.snd R S) I) := by
  apply Ideal.ext
  rintro ⟨r, s⟩
  rw [mem_prod, mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective,
    mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  refine ⟨fun h => ⟨⟨_, ⟨h, rfl⟩⟩, ⟨_, ⟨h, rfl⟩⟩⟩, ?_⟩
  rintro ⟨⟨⟨r, s'⟩, ⟨h₁, rfl⟩⟩, ⟨⟨r', s⟩, ⟨h₂, rfl⟩⟩⟩
  simpa using I.add_mem (I.mul_mem_left (1, 0) h₁) (I.mul_mem_left (0, 1) h₂)

@[simp]
/-
**Ideal.map_fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_fst_prod (I : Ideal R) (J : Ideal S) : map (RingHom.fst R S) (prod I J
) = I
参数：I : Ideal R；J : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
-/
theorem map_fst_prod (I : Ideal R) (J : Ideal S) : map (RingHom.fst R S) (prod I J) = I := by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.1, fun h => ⟨⟨x, 0⟩, ⟨⟨h, Ideal.zero_mem _⟩, rfl⟩⟩⟩

@[simp]
/-
**Ideal.map_snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_snd_prod (I : Ideal R) (J : Ideal S) : map (RingHom.snd R S) (prod I J
) = J
参数：I : Ideal R；J : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
-/
theorem map_snd_prod (I : Ideal R) (J : Ideal S) : map (RingHom.snd R S) (prod I J) = J := by
  ext x
  rw [mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  exact
    ⟨by
      rintro ⟨x, ⟨h, rfl⟩⟩
      exact h.2, fun h => ⟨⟨0, x⟩, ⟨⟨Ideal.zero_mem _, h⟩, rfl⟩⟩⟩

@[simp]
/-
**Ideal.map_prodComm_prod** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_prodComm_prod : map ((RingEquiv.prodComm : R × S ≃+* S × R) : R × S ->
+* S × R) (prod I J) = prod J I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ideal.ideal_prod_eq`：ideal_prod_eq (I : Ideal (R × S)) : I = Ideal.prod 
(map (RingHom.fst R S) I : Ideal R) (map (RingHom.snd R S) I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `RingEquiv.fst_comp_coe_prodComm`：fst_comp_coe_prodComm : (RingHom.fst S 
R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.snd R S
· 使用定理 `Ideal.map_snd_prod`：map_snd_prod (I : Ideal R) (J : Ideal S) : map (Ring
Hom.snd R S) (prod I J) = J
· 使用定理 `RingEquiv.snd_comp_coe_prodComm`：snd_comp_coe_prodComm : (RingHom.snd S 
R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.fst R S
· 使用定理 `Ideal.map_fst_prod`：map_fst_prod (I : Ideal R) (J : Ideal S) : map (Ring
Hom.fst R S) (prod I J) = I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_prodComm_prod :
    map ((RingEquiv.prodComm : R × S ≃+* S × R) : R × S →+* S × R) (prod I J) = prod J I := by
  refine Trans.trans (ideal_prod_eq _) ?_
  simp [map_map]

set_option backward.isDefEq.respectTransparency false in
/-- Ideals of `R × S` are in one-to-one correspondence with pairs of ideals of `R` and ideals of
`S`. -/
/-
**Ideal.idealProdEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：idealProdEquiv : Ideal (R × S) ≃o Ideal R × Ideal S where toFun I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ideals of `R × S` are in one-to-one correspondence with pairs of ideals of `R` a
nd ideals of
`S`.
-/
def idealProdEquiv : Ideal (R × S) ≃o Ideal R × Ideal S where
  toFun I := ⟨map (RingHom.fst R S) I, map (RingHom.snd R S) I⟩
  invFun I := prod I.1 I.2
  left_inv I := (ideal_prod_eq I).symm
  right_inv := fun ⟨I, J⟩ => by simp
  map_rel_iff' {I J} := by
    simp only [Equiv.coe_fn_mk, Prod.mk_le_mk]
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨map_mono h, map_mono h⟩⟩
    rw [ideal_prod_eq I, ideal_prod_eq J]
    exact inf_le_inf (comap_mono h.1) (comap_mono h.2)

@[simp]
/-
**Ideal.idealProdEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：idealProdEquiv_symm_apply (I : Ideal R) (J : Ideal S) : idealProdEquiv.sym
m ⟨I, J⟩ = prod I J
参数：I : Ideal R；J : Ideal S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idealProdEquiv_symm_apply (I : Ideal R) (J : Ideal S) :
    idealProdEquiv.symm ⟨I, J⟩ = prod I J :=
  rfl
/-
**Ideal.span_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：span_prod_le {s : Set R} {t : Set S} : span (s ×ˢ t) <= prod (span s) (spa
n t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ideal_prod_eq`：ideal_prod_eq (I : Ideal (R × S)) : I = Ideal.prod 
(map (RingHom.fst R S) I : Ideal R) (map (RingHom.snd R S) I)
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Ideal.prod_mono`：prod_mono {I₁ I₂ : Ideal R} {J₁ J₂ : Ideal S} (hI : I₁ 
<= I₂) (hJ : J₁ <= J₂) : prod I₁ J₁ <= prod I₂ J₂
· 使用定理 `Ideal.span_mono`：span_mono {s t : Set α} : s subseteq t -> span s <= spa
n t
· 使用定理 `Set.fst_image_prod_subset`：fst_image_prod_subset (s : Set α) (t : Set β)
 : Prod.fst '' s ×ˢ t subseteq s
· 使用定理 `Set.snd_image_prod_subset`：snd_image_prod_subset (s : Set α) (t : Set β)
 : Prod.snd '' s ×ˢ t subseteq t
-/
theorem span_prod_le {s : Set R} {t : Set S} :
    span (s ×ˢ t) ≤ prod (span s) (span t) := by
  rw [ideal_prod_eq (span (s ×ˢ t)), map_span, map_span]
  gcongr
  · exact Set.fst_image_prod_subset _ _
  · exact Set.snd_image_prod_subset _ _
/-
**Ideal.span_prod** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：span_prod {s : Set R} {t : Set S} (hst : s.Nonempty ↔ t.Nonempty) : span (
s ×ˢ t) = prod (span s) (span t)
参数：hst : s.Nonempty ↔ t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.ideal_prod_eq`：ideal_prod_eq (I : Ideal (R × S)) : I = Ideal.prod 
(map (RingHom.fst R S) I : Ideal R) (map (RingHom.snd R S) I)
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.fst_image_prod`：fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonem
pty) : Prod.fst '' s ×ˢ t = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.snd_image_prod`：snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Se
t β) : Prod.snd '' s ×ˢ t = t
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `Ideal.prod_bot_bot`：prod_bot_bot : prod (⊥ : Ideal R) (⊥ : Ideal S) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem span_prod {s : Set R} {t : Set S} (hst : s.Nonempty ↔ t.Nonempty) :
    span (s ×ˢ t) = prod (span s) (span t) := by
  simp_rw [iff_iff_and_or_not_and_not, Set.not_nonempty_iff_eq_empty] at hst
  obtain ⟨hs, ht⟩ | ⟨rfl, rfl⟩ := hst
  · conv_lhs => rw [Ideal.ideal_prod_eq (Ideal.span (s ×ˢ t))]
    congr 1
    · rw [Ideal.map_span]
      simp [Set.fst_image_prod _ ht]
    · rw [Ideal.map_span]
      simp [Set.snd_image_prod hs]
  · simp

@[simp]
/-
**Ideal.prod_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_inj {I I' : Ideal R} {J J' : Ideal S} : prod I J = prod I' J' ↔ I = I
' ∧ J = J'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_inj {I I' : Ideal R} {J J' : Ideal S} :
    prod I J = prod I' J' ↔ I = I' ∧ J = J' := by
  simp only [← idealProdEquiv_symm_apply, idealProdEquiv.symm.injective.eq_iff, Prod.mk_inj]

@[simp]
/-
**Ideal.prod_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_eq_bot_iff {I : Ideal R} {J : Ideal S} : prod I J = ⊥ ↔ I = ⊥ ∧ J = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.prod_inj`：prod_inj {I I' : Ideal R} {J J' : Ideal S} : prod I J = 
prod I' J' ↔ I = I' ∧ J = J'
· 使用定理 `Ideal.prod_bot_bot`：prod_bot_bot : prod (⊥ : Ideal R) (⊥ : Ideal S) = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_eq_bot_iff {I : Ideal R} {J : Ideal S} :
    prod I J = ⊥ ↔ I = ⊥ ∧ J = ⊥ := by
  rw [← prod_inj, prod_bot_bot]

@[simp]
/-
**Ideal.prod_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_eq_top_iff {I : Ideal R} {J : Ideal S} : prod I J = ⊤ ↔ I = ⊤ ∧ J = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.prod_inj`：prod_inj {I I' : Ideal R} {J J' : Ideal S} : prod I J = 
prod I' J' ↔ I = I' ∧ J = J'
· 使用定理 `Ideal.prod_top_top`：prod_top_top : prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_eq_top_iff {I : Ideal R} {J : Ideal S} :
    prod I J = ⊤ ↔ I = ⊤ ∧ J = ⊤ := by
  rw [← prod_inj, prod_top_top]
/-
**Ideal.isPrime_of_isPrime_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_of_isPrime_prod_top {I : Ideal R} (h : (Ideal.prod I (⊤ : Ideal S)
).IsPrime) : I.IsPrime
参数：h : (Ideal.prod I (⊤ : Ideal S)).IsPrime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.prod_top_top`：prod_top_top : prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤
· 使用定理 `Ideal.isPrime_iff`：isPrime_iff {I : Ideal α} : IsPrime I ↔ I != ⊤ ∧ fora
ll {x y : α}, x * y in I -> x in I ∨ y in I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Prod.mk_mul_mk`：mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) 
= (a₁ * a₂, b₁ * b₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ideal.mem_prod`：mem_prod {x : R × S} : x in prod I J ↔ x.1 in I ∧ x.2 in
 J
· 使用定理 `trivial`：True
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
theorem isPrime_of_isPrime_prod_top {I : Ideal R} (h : (Ideal.prod I (⊤ : Ideal S)).IsPrime) :
    I.IsPrime := by
  constructor
  · contrapose h
    rw [h, prod_top_top, isPrime_iff]
    simp
  · intro x y hxy
    have : (⟨x, 1⟩ : R × S) * ⟨y, 1⟩ ∈ prod I ⊤ := by
      rw [Prod.mk_mul_mk, mul_one, mem_prod]
      exact ⟨hxy, trivial⟩
    simpa using h.mem_or_mem this
/-
**Ideal.isPrime_of_isPrime_prod_top'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_of_isPrime_prod_top' {I : Ideal S} (h : (Ideal.prod (⊤ : Ideal R) 
I).IsPrime) : I.IsPrime
参数：h : (Ideal.prod (⊤ : Ideal R) I).IsPrime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isPrime_of_isPrime_prod_top`：isPrime_of_isPrime_prod_top {I : Idea
l R} (h : (Ideal.prod I (⊤ : Ideal S)).IsPrime) : I.IsPrime
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_prodComm_prod`：map_prodComm_prod : map ((RingEquiv.prodComm : 
R × S ≃+* S × R) : R × S ->+* S × R) (prod I J) = prod J I
-/
theorem isPrime_of_isPrime_prod_top' {I : Ideal S} (h : (Ideal.prod (⊤ : Ideal R) I).IsPrime) :
    I.IsPrime := by
  apply isPrime_of_isPrime_prod_top (S := R)
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := R) (S := S))
/-
**Ideal.isPrime_ideal_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_ideal_prod_top {I : Ideal R} [h : I.IsPrime] : (prod I (⊤ : Ideal 
S)).IsPrime where ne_top'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
theorem isPrime_ideal_prod_top {I : Ideal R} [h : I.IsPrime] : (prod I (⊤ : Ideal S)).IsPrime where
  ne_top' := by simpa using h.ne_top
  mem_or_mem' {x y} := by simpa using h.mem_or_mem
/-
**Ideal.isPrime_ideal_prod_top'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_ideal_prod_top' {I : Ideal S} [h : I.IsPrime] : (prod (⊤ : Ideal R
) I).IsPrime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isPrime_ideal_prod_top`：isPrime_ideal_prod_top {I : Ideal R} [h : 
I.IsPrime] : (prod I (⊤ : Ideal S)).IsPrime where ne_top'
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_prodComm_prod`：map_prodComm_prod : map ((RingEquiv.prodComm : 
R × S ≃+* S × R) : R × S ->+* S × R) (prod I J) = prod J I
-/
theorem isPrime_ideal_prod_top' {I : Ideal S} [h : I.IsPrime] : (prod (⊤ : Ideal R) I).IsPrime := by
  let : IsPrime (prod I (⊤ : Ideal R)) := isPrime_ideal_prod_top
  rw [← map_prodComm_prod]
  -- Note: couldn't synthesize the right instances without the `R` and `S` hints
  exact map_isPrime_of_equiv (RingEquiv.prodComm (R := S) (S := R))
/-
**Ideal.ideal_prod_prime_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ideal_prod_prime_aux {I : Ideal R} {J : Ideal S} : (Ideal.prod I J).IsPrim
e -> I = ⊤ ∨ J = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem ideal_prod_prime_aux {I : Ideal R} {J : Ideal S} :
    (Ideal.prod I J).IsPrime → I = ⊤ ∨ J = ⊤ := by
  contrapose!
  simp only [ne_top_iff_one, isPrime_iff, not_and, not_forall, not_or]
  exact fun ⟨hI, hJ⟩ _ => ⟨⟨0, 1⟩, ⟨1, 0⟩, by simp, by simp [hJ], by simp [hI]⟩

/-- Classification of prime ideals in product rings: the prime ideals of `R × S` are precisely the
    ideals of the form `p × S` or `R × p`, where `p` is a prime ideal of `R` or `S`. -/
/-
**Ideal.ideal_prod_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ideal_prod_prime (I : Ideal (R × S)) : I.IsPrime ↔ (exists p : Ideal R, p.
IsPrime ∧ I = Ideal.prod p ⊤) ∨ exists p : Ideal S, p.IsPrime ∧ I = Ideal.prod ⊤
 p
参数：I : Ideal (R × S)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ideal_prod_eq`：ideal_prod_eq (I : Ideal (R × S)) : I = Ideal.prod 
(map (RingHom.fst R S) I : Ideal R) (map (RingHom.snd R S) I)
· 使用定理 `Ideal.ideal_prod_prime_aux`：ideal_prod_prime_aux {I : Ideal R} {J : Idea
l S} : (Ideal.prod I J).IsPrime -> I = ⊤ ∨ J = ⊤
· 使用定理 `Ideal.isPrime_of_isPrime_prod_top'`：isPrime_of_isPrime_prod_top' {I : Id
eal S} (h : (Ideal.prod (⊤ : Ideal R) I).IsPrime) : I.IsPrime
· 使用定理 `Ideal.isPrime_of_isPrime_prod_top`：isPrime_of_isPrime_prod_top {I : Idea
l R} (h : (Ideal.prod I (⊤ : Ideal S)).IsPrime) : I.IsPrime
· 使用定理 `Ideal.isPrime_ideal_prod_top`：isPrime_ideal_prod_top {I : Ideal R} [h : 
I.IsPrime] : (prod I (⊤ : Ideal S)).IsPrime where ne_top'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.isPrime_ideal_prod_top'`：isPrime_ideal_prod_top' {I : Ideal S} [h 
: I.IsPrime] : (prod (⊤ : Ideal R) I).IsPrime

--- 原说明 ---
Classification of prime ideals in product rings: the prime ideals of `R × S` are
 precisely the
    ideals of the form `p × S` or `R × p`, where `p` is a prime ideal of `R` or 
`S`.
-/
theorem ideal_prod_prime (I : Ideal (R × S)) :
    I.IsPrime ↔
      (∃ p : Ideal R, p.IsPrime ∧ I = Ideal.prod p ⊤) ∨
        ∃ p : Ideal S, p.IsPrime ∧ I = Ideal.prod ⊤ p := by
  constructor
  · rw [ideal_prod_eq I]
    intro hI
    rcases ideal_prod_prime_aux hI with (h | h)
    · right
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top' hI, rfl⟩⟩
    · left
      rw [h] at hI ⊢
      exact ⟨_, ⟨isPrime_of_isPrime_prod_top hI, rfl⟩⟩
  · rintro (⟨p, ⟨h, rfl⟩⟩ | ⟨p, ⟨h, rfl⟩⟩)
    · exact isPrime_ideal_prod_top
    · exact isPrime_ideal_prod_top'

end Ideal

open Submodule.IsPrincipal in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsPrincipalIdealRing R] [IsPrincipalIdealRing S] : IsPrincipalIdealRing (R × S) where
  principal I := by
    rw [I.ideal_prod_eq, ← span_singleton_generator (I.map _),
      ← span_singleton_generator (I.map (RingHom.snd R S)), ← Ideal.span, ← Ideal.span,
      ← Ideal.span_prod (iff_of_true (by simp) (by simp)), Set.singleton_prod_singleton]
    exact ⟨_, rfl⟩
