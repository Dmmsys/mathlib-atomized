/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Group.Pi.Units

/-!
# Spectrum and quasispectrum of products

This file contains results regarding the spectra and quasispectra of (indexed) products of
elements of a (non-unital) ring. The main result is that the (quasi)spectrum of a product is the
union of the (quasi)spectra.

## Main declarations

+ `Pi.spectrum_eq`: `spectrum R a = ⋃ i, spectrum R (a i)` for `a : ∀ i, κ i`
+ `Prod.spectrum_eq`: `spectrum R ⟨a, b⟩ = spectrum R a ∪ spectrum R b`
+ `Pi.quasispectrum_eq`: `quasispectrum R a = ⋃ i, quasispectrum R (a i)` for `a : ∀ i, κ i`
+ `Prod.quasispectrum_eq`: `quasispectrum R ⟨a, b⟩ = quasispectrum R a ∪ quasispectrum R b`

## TODO

+ Apply these results to block matrices.

-/

@[expose] public section

variable {ι A B R : Type*} {κ : ι → Type*}

section quasiregular

variable (κ) in
/-- The equivalence between pre-quasiregular elements of an indexed product and the indexed product
of pre-quasiregular elements. -/
/-
**PreQuasiregular.toPi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PreQuasiregular.toPi [forall i, NonUnitalSemiring (κ i)] : PreQuasiregular
 (forall i, κ i) ≃* forall i, PreQuasiregular (κ i) where toFun
参数：κ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between pre-quasiregular elements of an indexed product and the 
indexed product
of pre-quasiregular elements.
-/
def PreQuasiregular.toPi [∀ i, NonUnitalSemiring (κ i)] :
    PreQuasiregular (∀ i, κ i) ≃* ∀ i, PreQuasiregular (κ i) where
  toFun := fun x i => .mk <| x.val i
  invFun := fun x => .mk <| fun i => (x i).val
  map_mul' _ _ := rfl

variable (A B) in
/-- The equivalence between pre-quasiregular elements of a product and the product of
pre-quasiregular elements. -/
/-
**PreQuasiregular.toProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PreQuasiregular.toProd [NonUnitalSemiring A] [NonUnitalSemiring B] : PreQu
asiregular (A × B) ≃* PreQuasiregular A × PreQuasiregular B where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between pre-quasiregular elements of a product and the product o
f
pre-quasiregular elements.
-/
def PreQuasiregular.toProd [NonUnitalSemiring A] [NonUnitalSemiring B] :
    PreQuasiregular (A × B) ≃* PreQuasiregular A × PreQuasiregular B where
  toFun := fun p => ⟨.mk p.val.1, .mk p.val.2⟩
  invFun := fun ⟨a, b⟩ => .mk ⟨a.val, b.val⟩
  map_mul' _ _ := rfl
/-
**isQuasiregular_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isQuasiregular_pi_iff [forall i, NonUnitalSemiring (κ i)] (x : forall i, κ
 i) : IsQuasiregular x ↔ forall i, IsQuasiregular (x i)
参数：κ i；x : forall i, κ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma isQuasiregular_pi_iff [∀ i, NonUnitalSemiring (κ i)] (x : ∀ i, κ i) :
    IsQuasiregular x ↔ ∀ i, IsQuasiregular (x i) := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toPi κ), Pi.isUnit_iff]
  congr!
/-
**isQuasiregular_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isQuasiregular_prod_iff [NonUnitalSemiring A] [NonUnitalSemiring B] (a : A
) (b : B) : IsQuasiregular (⟨a, b⟩ : A × B) ↔ IsQuasiregular a ∧ IsQuasiregular 
b
参数：a : A；b : B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma isQuasiregular_prod_iff [NonUnitalSemiring A] [NonUnitalSemiring B] (a : A) (b : B) :
    IsQuasiregular (⟨a, b⟩ : A × B) ↔ IsQuasiregular a ∧ IsQuasiregular b := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toProd A B), Prod.isUnit_iff]
  congr!
/-
**quasispectrum.mem_iff_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum.mem_iff_of_isUnit [CommSemiring R] [NonUnitalRing A] [Module
 R A] {a : A} {r : R} (hr : IsUnit r) : r in quasispectrum R a ↔ ¬ IsQuasiregula
r (-(hr.unit⁻¹ • a))
参数：hr : IsUnit r。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasispectrum.mem_iff_of_isUnit [CommSemiring R] [NonUnitalRing A]
    [Module R A] {a : A} {r : R} (hr : IsUnit r) :
    r ∈ quasispectrum R a ↔ ¬ IsQuasiregular (-(hr.unit⁻¹ • a)) :=
  ⟨fun h => h hr, fun h _ => h⟩

end quasiregular

section spectrum

/-
**Pi.spectrum_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.spectrum_eq [CommSemiring R] [forall i, Ring (κ i)] [forall i, Algebra 
R (κ i)] (a : forall i, κ i) : spectrum R a = ⋃ i, spectrum R (a i)
参数：κ i；κ i；a : forall i, κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_ofPred`：iInter_ofPred (P : ι -> α -> Prop) : ⋂ i, { x : α | P
 i x } = { x : α | forall i, P i x }
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.spectrum_eq [CommSemiring R] [∀ i, Ring (κ i)] [∀ i, Algebra R (κ i)]
    (a : ∀ i, κ i) : spectrum R a = ⋃ i, spectrum R (a i) := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_iUnion, compl_compl, resolventSet, Set.iInter_ofPred,
    Pi.isUnit_iff, sub_apply, algebraMap_apply]
/-
**Prod.spectrum_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prod.spectrum_eq [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra
 R B] (a : A) (b : B) : spectrum R (⟨a, b⟩ : A × B) = spectrum R a union spectru
m R b
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Prod.spectrum_eq [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (a : A) (b : B) : spectrum R (⟨a, b⟩ : A × B) = spectrum R a ∪ spectrum R b := by
  apply compl_injective
  simp_rw [spectrum, Set.compl_union, compl_compl, resolventSet, ← Set.ofPred_and,
    Prod.isUnit_iff, algebraMap_apply, mk_sub_mk]
/-
**Pi.quasispectrum_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.quasispectrum_eq [Nonempty ι] [CommSemiring R] [forall i, NonUnitalRing
 (κ i)] [forall i, Module R (κ i)] (a : forall i, κ i) : quasispectrum R a = ⋃ i
, quasispectrum R (a i)
参数：κ i；κ i；a : forall i, κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsUnit.unit_of_val_units`：unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)
) : h.unit = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma Pi.quasispectrum_eq [Nonempty ι] [CommSemiring R] [∀ i, NonUnitalRing (κ i)]
    [∀ i, Module R (κ i)] (a : ∀ i, κ i) :
    quasispectrum R a = ⋃ i, quasispectrum R (a i) := by
  ext r
  simp only [quasispectrum, Set.mem_ofPred_eq, Set.mem_iUnion]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_pi_iff]
  · simp [hr]
/-
**Prod.quasispectrum_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prod.quasispectrum_eq [CommSemiring R] [NonUnitalRing A] [NonUnitalRing B]
 [Module R A] [Module R B] (a : A) (b : B) : quasispectrum R (⟨a, b⟩ : A × B) = 
quasispectrum R a union quasispectrum R b
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsUnit.unit_of_val_units`：unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)
) : h.unit = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma Prod.quasispectrum_eq [CommSemiring R] [NonUnitalRing A] [NonUnitalRing B]
    [Module R A] [Module R B] (a : A) (b : B) :
    quasispectrum R (⟨a, b⟩ : A × B) = quasispectrum R a ∪ quasispectrum R b := by
  apply compl_injective
  ext r
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not,
    Set.mem_union]
  by_cases hr : IsUnit r
  · lift r to Rˣ using hr with r' hr'
    simp [isQuasiregular_prod_iff]
  · simp [hr]

end spectrum

