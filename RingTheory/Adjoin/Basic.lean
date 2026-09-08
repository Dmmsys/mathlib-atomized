/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Order.Group.Nat
/-!
# Adjoining elements to form subalgebras

This file contains basic results on `Algebra.adjoin`.

## Tags

adjoin, algebra

-/

public section

assert_not_exists Polynomial

universe uR uS uA uB

open Module Submodule Subsemiring
open scoped Pointwise

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

namespace Algebra

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]
variable {s t : Set A}

variable (R A)

variable {A} (s)

/-
**Algebra.adjoin_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_prod_le (s : Set A) (t : Set B) : adjoin R (s ×ˢ t) <= (adjoin R s)
.prod (adjoin R t)
参数：s : Set A；t : Set B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem adjoin_prod_le (s : Set A) (t : Set B) :
    adjoin R (s ×ˢ t) ≤ (adjoin R s).prod (adjoin R t) :=
  adjoin_le <| Set.prod_mono subset_adjoin subset_adjoin
/-
**Algebra.adjoin_inl_union_inr_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_inl_union_inr_eq_prod (s) (t) : adjoin R (LinearMap.inl R A B '' (s
 union {1}) union LinearMap.inr R A B '' (t union {1})) = (adjoin R s).prod (adj
oin R t)
参数：s；t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.mk_preimage_prod_left`：mk_preimage_prod_left (hb : b in t) : (fun a 
=> (a, b)) ⁻¹' s ×ˢ t = s
· 使用定理 `Set.mk_preimage_prod_right`：mk_preimage_prod_right (ha : a in s) : Prod.
mk a ⁻¹' s ×ˢ t = t
· 使用定理 `Algebra.mem_adjoin_of_map_mul`：mem_adjoin_of_map_mul {s} {x : A} {f : A 
->ₗ[R] B} (hf : forall a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) (h : x in adjoin R s) :
 f x in adjoin R (f…
· 使用定理 `LinearMap.inl_map_mul`：inl_map_mul (a₁ a₂ : A) : LinearMap.inl R A B (a₁
 * a₂) = LinearMap.inl R A B a₁ * LinearMap.inl R A B a₂
· 使用定理 `LinearMap.inr_map_mul`：inr_map_mul (b₁ b₂ : B) : LinearMap.inr R A B (b₁
 * b₂) = LinearMap.inr R A B b₁ * LinearMap.inr R A B b₂
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
-/
theorem adjoin_inl_union_inr_eq_prod (s) (t) :
    adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1})) =
      (adjoin R s).prod (adjoin R t) := by
  apply le_antisymm
  · simp only [adjoin_le_iff, Set.insert_subset_iff, Subalgebra.zero_mem, Subalgebra.one_mem,
      subset_adjoin, -- the rest comes from `squeeze_simp`
      Set.union_subset_iff,
      LinearMap.coe_inl, Set.mk_preimage_prod_right, Set.image_subset_iff, SetLike.mem_coe,
      Set.mk_preimage_prod_left, LinearMap.coe_inr, and_self_iff, Set.union_singleton,
      Subalgebra.coe_prod]
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    let P := adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}))
    have Ha : (a, (0 : B)) ∈ adjoin R (LinearMap.inl R A B '' (s ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inl_map_mul ha
    have Hb : ((0 : A), b) ∈ adjoin R (LinearMap.inr R A B '' (t ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inr_map_mul hb
    replace Ha : (a, (0 : B)) ∈ P := adjoin_mono Set.subset_union_left Ha
    replace Hb : ((0 : A), b) ∈ P := adjoin_mono Set.subset_union_right Hb
    simpa [P] using Subalgebra.add_mem _ Ha Hb

variable (A) in
/-
**Algebra.adjoin_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_algebraMap (s : Set S) : adjoin R (algebraMap S A '' s) = (adjoin R
 s).map (IsScalarTower.toAlgHom R S A)
参数：s : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
-/
theorem adjoin_algebraMap (s : Set S) :
    adjoin R (algebraMap S A '' s) = (adjoin R s).map (IsScalarTower.toAlgHom R S A) :=
  adjoin_image R (IsScalarTower.toAlgHom R S A) s
/-
**Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra`。
形式化陈述：adjoin_algebraMap_image_union_eq_adjoin_adjoin (s : Set S) (t : Set A) : a
djoin R (algebraMap S A '' s union t) = (adjoin (adjoin R s) t).restrictScalars 
R
参数：s : Set S；t : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subsemiring.closure_mono`：closure_mono ⦃s t : Set R⦄ (h : s subseteq t) 
: closure s <= closure t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Set.union_subset_union_left`：union_subset_union_left {s₁ s₂ : Set α} (t)
 (h : s₁ subseteq s₂) : s₁ union t subseteq s₂ union t
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Algebra.adjoin_algebraMap`：adjoin_algebraMap (s : Set S) : adjoin R (alg
ebraMap S A '' s) = (adjoin R s).map (IsScalarTower.toAlgHom R S A)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem adjoin_algebraMap_image_union_eq_adjoin_adjoin (s : Set S) (t : Set A) :
    adjoin R (algebraMap S A '' s ∪ t) = (adjoin (adjoin R s) t).restrictScalars R :=
  le_antisymm
    (closure_mono <|
      Set.union_subset (Set.range_subset_iff.2 fun r => Or.inl ⟨algebraMap R (adjoin R s) r,
        (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩)
        (Set.union_subset_union_left _ fun _ ⟨_x, hx, hxs⟩ => hxs ▸ ⟨⟨_, subset_adjoin hx⟩, rfl⟩))
    (closure_le.2 <|
      Set.union_subset (Set.range_subset_iff.2 fun x => adjoin_mono Set.subset_union_left <|
        Algebra.adjoin_algebraMap R A s ▸ ⟨x, x.prop, rfl⟩)
        (Set.Subset.trans Set.subset_union_right subset_adjoin))
/-
**Algebra.adjoin_adjoin_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_adjoin_of_tower (s : Set A) : adjoin S (adjoin R s : Set A) = adjoi
n S s
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.coe_restrictScalars`：coe_restrictScalars {U : Subalgebra S A}
 : (restrictScalars R U : Set A) = (U : Set A)
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
-/
theorem adjoin_adjoin_of_tower (s : Set A) : adjoin S (adjoin R s : Set A) = adjoin S s := by
  apply le_antisymm (adjoin_le _)
  · exact adjoin_mono subset_adjoin
  · rw [← Subalgebra.coe_restrictScalars R (S := S), SetLike.coe_subset_coe]
    exact adjoin_le subset_adjoin
/-
**Algebra.Subalgebra.restrictScalars_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.S
ubalgebra`。
形式化陈述：∀ (R : Type uR) {S : Type uS} {A : Type uA} [inst : CommSemiring R] [inst_
1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Algebra R S] [inst_4 : Alg
ebra R A] [inst_5 : Algebra S A] [inst_6 : IsScalarTower R S A] {s : Set A},   S
ubalgebra.restrictScalars R (Algebra.adjoin S s) = (IsScalarTower.toAlgHom R S A
).range ⊔ Algebra.adjoin R s
参数：R : Type uR；Algebra.adjoin S s；IsScalarTower.toAlgHom R S A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subalgebra.mem_restrictScalars`：mem_restrictScalars {U : Subalgebra S A}
 {x : A} : x in restrictScalars R U ↔ x in U
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
-/
theorem Subalgebra.restrictScalars_adjoin {s : Set A} :
    (adjoin S s).restrictScalars R = (IsScalarTower.toAlgHom R S A).range ⊔ adjoin R s := by
  refine le_antisymm (fun _ hx ↦ adjoin_induction
    (fun x hx ↦ le_sup_right (α := Subalgebra R A) (subset_adjoin hx))
    (fun x ↦ le_sup_left (α := Subalgebra R A) ⟨x, rfl⟩)
    (fun _ _ _ _ ↦ add_mem) (fun _ _ _ _ ↦ mul_mem) <|
    (Subalgebra.mem_restrictScalars _).mp hx) (sup_le ?_ <| adjoin_le subset_adjoin)
  rintro _ ⟨x, rfl⟩; exact algebraMap_mem (adjoin S s) x

@[simp]
/-
**Algebra.adjoin_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_top {A} [Semiring A] [Algebra S A] (t : Set A) : adjoin (⊤ : Subalg
ebra R S) t = (adjoin S t).restrictScalars (⊤ : Subalgebra R S)
参数：t : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `trivial`：True
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderIso.symm_apply_le`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [i
nst_1 : LE β] (e : α ≃o β) {x : α} {y : β}, e.symm y ≤ x ↔ y ≤ e x
-/
theorem adjoin_top {A} [Semiring A] [Algebra S A] (t : Set A) :
    adjoin (⊤ : Subalgebra R S) t = (adjoin S t).restrictScalars (⊤ : Subalgebra R S) :=
  let equivTop : Subalgebra (⊤ : Subalgebra R S) A ≃o Subalgebra S A :=
    { toFun := fun s => { s with algebraMap_mem' := fun r => s.algebraMap_mem ⟨r, trivial⟩ }
      invFun := fun s => s.restrictScalars _
      left_inv := fun _ => SetLike.coe_injective rfl
      right_inv := fun _ => SetLike.coe_injective rfl
      map_rel_iff' := @fun _ _ => Iff.rfl }
  le_antisymm
    (adjoin_le <| show t ⊆ adjoin S t from subset_adjoin)
    (equivTop.symm_apply_le.mpr <|
      adjoin_le <| show t ⊆ adjoin (⊤ : Subalgebra R S) t from subset_adjoin)

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A]
variable [Algebra R A] {s t : Set A}
variable (R s t)

/-
**Algebra.adjoin_union_eq_adjoin_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_union_eq_adjoin_adjoin : adjoin R (s union t) = (adjoin (adjoin R s
) t).restrictScalars R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin`：adjoin_algebraMa
p_image_union_eq_adjoin_adjoin (s : Set S) (t : Set A) : adjoin R (algebraMap S 
A '' s union t) = (adjoin (adjoin R s) t).re…
-/
theorem adjoin_union_eq_adjoin_adjoin :
    adjoin R (s ∪ t) = (adjoin (adjoin R s) t).restrictScalars R := by
  simpa using adjoin_algebraMap_image_union_eq_adjoin_adjoin R s t

/--
If `A` is spanned over `R` by `s`, then the algebra spanned over `A` by `t` is the equal to the
algebra spanned over `R` by `s ∪ t`.
-/
/-
**Algebra.adjoin_eq_adjoin_union** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_eq_adjoin_union [CommSemiring B] [Algebra R B] [Algebra A B] [IsSca
larTower R A B] (s : Set A) (t : Set B) (hS : adjoin R s = ⊤) : (adjoin A t).res
trictScalars R = adjoin R ((algebraMap A B '' s) union t)
参数：s : Set A；t : Set B；hS : adjoin R s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_union_eq_adjoin_adjoin`：adjoin_union_eq_adjoin_adjoin : a
djoin R (s union t) = (adjoin (adjoin R s) t).restrictScalars R
· 使用定理 `IsScalarTower.coe_toAlgHom'`：coe_toAlgHom' : (toAlgHom R S A : S -> A) =
 algebraMap S A
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.adjoin_range_toAlgHom`：adjoin_range_toAlgHom (t : Set A) :
 (Algebra.adjoin (toAlgHom R S A).range t).restrictScalars R = (Algebra.adjoin S
 t).restrictScalars R

--- 原说明 ---
If `A` is spanned over `R` by `s`, then the algebra spanned over `A` by `t` is t
he equal to the
algebra spanned over `R` by `s ∪ t`.
-/
theorem adjoin_eq_adjoin_union [CommSemiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (s : Set A) (t : Set B) (hS : adjoin R s = ⊤) :
    (adjoin A t).restrictScalars R = adjoin R ((algebraMap A B '' s) ∪ t) := by
  have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom R A B)) hS
  rw [Algebra.map_top, AlgHom.map_adjoin, IsScalarTower.coe_toAlgHom'] at this
  rw [adjoin_union_eq_adjoin_adjoin, this, ← IsScalarTower.adjoin_range_toAlgHom]

variable {R}
/-
**Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra`。
形式化陈述：pow_smul_mem_of_smul_subset_of_mem_adjoin [CommSemiring B] [Algebra R B] [
Algebra A B] [IsScalarTower R A B] (r : A) (s : Set B) (B' : Subalgebra R B) (hs
 : r • s subseteq B') {x : B} (hx : x in adjoin R s) (hr : algebraMap A B r in B
') : exists n₀ : Nat, forall n >= n₀, r ^ n • x in B'
参数：r : A；s : Set B；B' : Subalgebra R B；hs : r • s subseteq B'；hx : x in adjoin R
 s；hr : algebraMap A B r in B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_span_iff_linearCombination`：mem_span_iff_linearCombination (
s : Set M) (x : M) : x in span R s ↔ exists l : s ->₀ R, linearCombination R (↑)
 l = x
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.pow_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x : A}, x ∈
 S → ∀ (…
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `Submonoid.closure_mono`：closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : 
closure s <= closure t
· 使用定理 `Submonoid.pow_smul_mem_closure_smul`：pow_smul_mem_closure_smul {N : Type
*} [CommMonoid N] [MulAction M N] [IsScalarTower M N N] (r : M) (s : Set N) {x :
 N} (hx : x in closure s)…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem pow_smul_mem_of_smul_subset_of_mem_adjoin [CommSemiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (r : A) (s : Set B) (B' : Subalgebra R B) (hs : r • s ⊆ B') {x : B}
    (hx : x ∈ adjoin R s) (hr : algebraMap A B r ∈ B') : ∃ n₀ : ℕ, ∀ n ≥ n₀, r ^ n • x ∈ B' := by
  change x ∈ Subalgebra.toSubmodule (adjoin R s) at hx
  rw [adjoin_eq_span, Finsupp.mem_span_iff_linearCombination] at hx
  rcases hx with ⟨l, rfl : (l.sum fun (i : Submonoid.closure s) (c : R) => c • (i : B)) = x⟩
  choose n₁ n₂ using fun x : Submonoid.closure s => Submonoid.pow_smul_mem_closure_smul r s x.prop
  use l.support.sup n₁
  intro n hn
  rw [Finsupp.smul_sum]
  refine B'.toSubmodule.sum_mem ?_
  intro a ha
  have : n ≥ n₁ a := le_trans (Finset.le_sup ha) hn
  dsimp only
  rw [← tsub_add_cancel_of_le this, pow_add, ← smul_smul, ←
    IsScalarTower.algebraMap_smul A (l a) (a : B), smul_smul (r ^ n₁ a), mul_comm, ← smul_smul,
    smul_def, map_pow, IsScalarTower.algebraMap_smul]
  apply Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) _
  refine Subalgebra.smul_mem _ ?_ _
  change _ ∈ B'.toSubmonoid
  rw [← Submonoid.closure_eq B'.toSubmonoid]
  apply Submonoid.closure_mono hs (n₂ a)
/-
**Algebra.pow_smul_mem_adjoin_smul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：pow_smul_mem_adjoin_smul (r : R) (s : Set A) {x : A} (hx : x in adjoin R s
) : exists n₀ : Nat, forall n >= n₀, r ^ n • x in adjoin R (r • s)
参数：r : R；s : Set A；hx : x in adjoin R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin`：pow_smul_mem_of_smul_
subset_of_mem_adjoin [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower
 R A B] (r : A) (s : Set B) (B' : Subal…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
-/
theorem pow_smul_mem_adjoin_smul (r : R) (s : Set A) {x : A} (hx : x ∈ adjoin R s) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, r ^ n • x ∈ adjoin R (r • s) :=
  pow_smul_mem_of_smul_subset_of_mem_adjoin r s _ subset_adjoin hx (Subalgebra.algebraMap_mem _ _)
/-
**Algebra.adjoin_nonUnitalSubalgebra_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`
。
形式化陈述：adjoin_nonUnitalSubalgebra_eq_span (s : NonUnitalSubalgebra R A) : Subalge
bra.toSubmodule (adjoin R (s : Set A)) = span R {1} ⊔ s.toSubmodule
参数：s : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用引理 `Submonoid.closure_eq_one_union`：closure_eq_one_union (s : Set M) : closu
re s = {(1 : M)} union (Subsemigroup.closure s : Set M)
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NonUnitalAlgebra.adjoin_eq_span`：adjoin_eq_span (s : Set A) : (adjoin R 
s).toSubmodule = span R (Subsemigroup.closure s)
· 使用引理 `NonUnitalAlgebra.adjoin_eq`：adjoin_eq (s : NonUnitalSubalgebra R A) : ad
join R (s : Set A) = s
-/
lemma adjoin_nonUnitalSubalgebra_eq_span (s : NonUnitalSubalgebra R A) :
    Subalgebra.toSubmodule (adjoin R (s : Set A)) = span R {1} ⊔ s.toSubmodule := by
  rw [adjoin_eq_span, Submonoid.closure_eq_one_union, span_union, ← NonUnitalAlgebra.adjoin_eq_span,
      NonUnitalAlgebra.adjoin_eq]

end CommSemiring

end Algebra

open Algebra Subalgebra

section

variable (F E : Type*) {K : Type*} [CommSemiring E] [Semiring K] [SMul F E] [Algebra E K]

variable [CommSemiring F] [Algebra F K] [IsScalarTower F E K] (L : Subalgebra F K) {F}

/-- If `K / E / F` is a ring extension tower, `L` is a subalgebra of `K / F`,
then `E[L]` is generated by any basis of `L / F` as an `E`-module. -/
/-
**Subalgebra.adjoin_eq_span_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.adjoin_eq_span_basis {ι : Type*} (bL : Basis ι F L) : toSubmodu
le (adjoin E (L : Set K)) = span E (Set.range fun i : ι => (bL i).1)
参数：bL : Basis ι F L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.adjoin_eq_span_of_eq_span`：Subalgebra.adjoin_eq_span_of_eq_sp
an {S : Set K} (h : toSubmodule L = span F S) : toSubmodule (adjoin E (L : Set K
)) = span E S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.range_val`：range_val : S.val.range = S
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…

--- 原说明 ---
If `K / E / F` is a ring extension tower, `L` is a subalgebra of `K / F`,
then `E[L]` is generated by any basis of `L / F` as an `E`-module.
-/
theorem Subalgebra.adjoin_eq_span_basis {ι : Type*} (bL : Basis ι F L) :
    toSubmodule (adjoin E (L : Set K)) = span E (Set.range fun i : ι ↦ (bL i).1) :=
  L.adjoin_eq_span_of_eq_span E <| by
    simpa only [← L.range_val, Submodule.map_span, Submodule.map_top, ← Set.range_comp]
      using! congr_arg (Submodule.map (L.val : L →ₗ[F] K)) bL.span_eq.symm
/-
**Algebra.restrictScalars_adjoin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.restrictScalars_adjoin (F : Type*) [CommSemiring F] {E : Type*} [C
ommSemiring E] [Algebra F E] (K : Subalgebra F E) (S : Set E) : (Algebra.adjoin 
K S).restrictScalars F = Algebra.adjoin F (K union S)
参数：F : Type*；K : Subalgebra F E；S : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_eq`：adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S
· 使用定理 `Algebra.adjoin_union_eq_adjoin_adjoin`：adjoin_union_eq_adjoin_adjoin : a
djoin R (s union t) = (adjoin (adjoin R s) t).restrictScalars R
-/
theorem Algebra.restrictScalars_adjoin (F : Type*) [CommSemiring F] {E : Type*} [CommSemiring E]
    [Algebra F E] (K : Subalgebra F E) (S : Set E) :
    (Algebra.adjoin K S).restrictScalars F = Algebra.adjoin F (K ∪ S) := by
  conv_lhs => rw [← Algebra.adjoin_eq K, ← Algebra.adjoin_union_eq_adjoin_adjoin]

/-- If `E / L / F` and `E / L' / F` are two ring extension towers, `L ≃ₐ[F] L'` is an isomorphism
compatible with `E / L` and `E / L'`, then for any subset `S` of `E`, `L[S]` and `L'[S]` are
equal as subalgebras of `E / F`. -/
/-
**Algebra.restrictScalars_adjoin_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.restrictScalars_adjoin_of_algEquiv {F E L L' : Type*} [CommSemirin
g F] [CommSemiring L] [CommSemiring L'] [Semiring E] [Algebra F L] [Algebra L E]
 [Algebra F L'] [Algebra L' E] [Algebra F E] [IsScalarTower F L E] [IsScalarTowe
r F L' E] (i : L ≃ₐ[F] L') (hi : algebraMap L E = (algebraMap L' E) ∘ i) (S : Se
t E) : (Algebra.adjoin L S).restrictScalars F = (Algebra.adjoin L' S).restrictSc
alars F
参数：i : L ≃ₐ[F] L'；hi : algebraMap L E = (algebraMap L' E) ∘ i；S : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
If `E / L / F` and `E / L' / F` are two ring extension towers, `L ≃ₐ[F] L'` is a
n isomorphism
compatible with `E / L` and `E / L'`, then for any subset `S` of `E`, `L[S]` and
 `L'[S]` are
equal as subalgebras of `E / F`.
-/
theorem Algebra.restrictScalars_adjoin_of_algEquiv
    {F E L L' : Type*} [CommSemiring F] [CommSemiring L] [CommSemiring L'] [Semiring E]
    [Algebra F L] [Algebra L E] [Algebra F L'] [Algebra L' E] [Algebra F E]
    [IsScalarTower F L E] [IsScalarTower F L' E] (i : L ≃ₐ[F] L')
    (hi : algebraMap L E = (algebraMap L' E) ∘ i) (S : Set E) :
    (Algebra.adjoin L S).restrictScalars F = (Algebra.adjoin L' S).restrictScalars F := by
  apply_fun Subalgebra.toSubsemiring using fun K K' h ↦ by rwa [SetLike.ext'_iff] at h ⊢
  change Subsemiring.closure _ = Subsemiring.closure _
  rw [hi, Set.range_comp, EquivLike.range_eq_univ, Set.image_univ]

end

